# W2_SFTC_REPORT — unit U112-C (`sftc_`), leaf `sft_same_sign` — PROVED (2026-09-15 18:47 UTC / 2:47pM ET)

Prover subagent (wave 2).  File: `work/drafts/corner/W2_SFTC.lean` = `Partial_Assembled.lean` (sha256 `85312954…`)
with ONE pure insertion and ONE leaf body; sha256 `41540943…`, 8136 lines.  Nothing written under work/lean.

## 0. Result

| item | value |
|---|---|
| leaf | `SM.sft_same_sign` (frozen statement, W2_SFTC.lean:7807-7811) — **PROVED** (body :7812-7865, 54 lines) |
| helpers | 36 declarations, prefix `sftc_` (33 theorems, 3 defs), W2_SFTC.lean:7110-7802, immediately before the leaf's docstring, inside `section Soft` |
| compile | `cd work/lean && lake env lean ../drafts/corner/W2_SFTC.lean`: **0 errors**, 23 s (warm, load ≈ 8); 23 warnings = **9 `declaration uses sorry`** (the 9 open bodies below) + 14 pre-existing linter/deprecation warnings, all inside the U_SFTA block (lines 5802-6714, PARTIAL_ASSEMBLY_REPORT §5); **no warning in the `sftc_` block or the leaf body** |
| `grep -c sorry` | before **12** (10 bodies + 2 prose mentions, lines 25 and 8103) → after **11** (9 bodies + the same 2 prose lines) |
| remaining `sorry` bodies | `sg_daughters_products` :691, `s7_sliding_law_at` :4243, `s7_bigon_law_at` :5409, `s7_corner_product` :5565, `sft_loop` :8018, and the §6 row theorems `cb_singleton` :8109, `corner_values` :8114, `thm_C_S7` :8119, `thm_C_soft` :8124 — none touched |
| `#print axioms SM.sft_same_sign` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — **no `sorryAx`**; exactly PLAN_FINAL §4's expected list (`lp_lm`/`lp_lm_uniqueness` enter through `P_eq_homfly`, lp:core, as for `corner_values_i`) |
| `#print axioms SM.sftc_homfly_eq` | same six |
| `#print axioms SM.sftc_rotation_eventually` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms SM.thm_C_soft_of_cornerValues` | still `sorryAx` — through `sft_loop` (U112-D) only; `sft_same_sign` and `sft_mixed` are closed |
| statements | `python3 tools/stmt_check.py W2_SFTC.lean`: **49/49 PASS**, exit 0 |
| diff vs Partial_Assembled.lean | hunks `7109a7110,7802` (helper block) and `7119c7812,7865` (leaf body); the ONLY removed line is `  sorry` |
| imports | unchanged (no import added) |

The leaf is TRUE as stated; no hypothesis is missing.  `hq` is used only through `soft_family_generic`; `hs` (the
same-sign sector) is used three times: to exclude the loop sector (`hnot`), for the vertex turns `−χ₋ = −χ₊ = τ`, and
for the sign data of the angle-addition step.

## 1. Route (PLAN_FINAL §3.4 "Same-sign", adapted)

The transport `sfta_softTransport` (U112-A) already reduces the leaf to two per-carrier inputs of
`sfta_InsertMarkTransport.cornerStateSum_transport`: for every decomposition `S` and carrier `q`,
(a) `carrierRotation` equal and (b) `homfly` of the positive lifts equal (`cornerCoefficient_transport`); uniformity
is `carrierUniform_iff` from the carried mark turns (`sfta_softTransport_markTurn`, with `−χ₋ = τ` at `μ_j`) and
`turn P_ε M_ε = −χ₊ = τ`; the sign is `leftTurns_transport`: `ℓ(P_ε) = ℓ(P) + [τ = 1]`, so
`(−1)^{ℓ(P_ε)+ℓ(P)} = −τ`.

**(b) HOMFLY — combinatorial, no deformation.**  PLAN §3.4 proposed CS3 §A's flat-subdivision `Reparam` + a `Deform`
(a geometric family with constant crossing set); instead the accepted record layer closes it without geometry:
`P_eq_homfly` (lp:core) turns `homfly` into the record polynomial `P`; `presentations` (lc:presentations,
PolynomialBlock.lean:1177) makes `P` invariant under `RecordIso`; `CB.positiveLiftRecordIso` (cb:products KL1,
CBProducts.lean:946) identifies the record of a carrier's positive lift with the abstract Gauss record
`CB.gaussRecord (CB.cg …) (carrierCrossings …)`; and `sftc_gaussRecordIso` is the isomorphism of the two Gauss
records: occurrences by the inherited-visit bijection, successor because the key-sorted restricted Gauss list of
`P_ε` is LITERALLY the parent list mapped (`sftc_gaussList_map`: keys compare as the parent keys by
`sfta_soft_visitKey_lt_iff`, i.e. lem:soft-generic's same-edge order clause; sorted nodup lists with the same members
are equal), pairing by `twin_eq`, over bits by the inherited crossing signs (lem:soft-generic (iii)), signs all `+1`.
This is the printed "same Gauss word ⇒ same record ⇒ same polynomial" (sm-4:1047-1052) taken literally.

**(a) Rotation — analytic, the ε → 0 limit.**  `sge_rotation_eq_sum` (U103-E, already in the file):
`2π r_Q = Σ_{m corner mark of Q} ∠(edge P (in m), edge P (out m))`.  In `P_ε` every transported corner `m ≠ μ_j` has
the turn `∠(dir_ε(in m), dir_ε(out m))` where `dir_ε e = edge P e` except `dir_ε j = v − ε q` (the return edge;
`sftc_edge_softParentEdge`, `sftc_markPrincipalTurn_toMark`), and the two corners `μ_j, M_ε` of the carrier through the
attachment MERGE: `∠(u, q) + ∠(q, v − εq) = ∠(u, v − εq) = ∠(dir_ε(j−1), dir_ε j)` by angle addition
(`sftc_principalAngle_add`: the three angles agree mod `2π` by `principalAngle_coe_angle`, all have the sign `τ` —
`−χ₋`, `−χ₊` and lem:soft-generic (ii)'s return-edge sign `sgn det(u, v − εq) = τ` — so the multiple of `2π` is `0`;
this is sm-4:1040-1046).  Hence `2π r_{Q_ε} = F_{S,q}(ε) := Σ_{m ∈ cornerSet q} ∠(dir_ε(in m), dir_ε(out m))`
(`sftc_rotation_mul_two_pi`), an explicit function of the real `ε` built from `P` alone, with `F(0) = 2π r_q` and
`F` continuous at `0` (`continuousAt_principalAngle` on the regular pairs `ccp_corner_directions_det_ne_zero`).
Both rotations are integers (lem:rot), so `|F(ε) − F(0)| < 2π` forces equality; `Filter.eventually_all` over the
finite type `Σ S, Component hn hP S` gives one `δ` for all `(S, q)` (`sftc_rotation_eventually`).  The printed
"principal-angle addition in the turn wedge + `rotationNumber_integer` for small ε" (PLAN §3.4) is rendered exactly
this way; no deformation of corner polygons is needed.

## 2. The 36 helpers (W2_SFTC.lean:7110-7802), by section

| section | declaration | content |
|---|---|---|
| SftcData | `sftc_soft_data` | `sfta_soft_data` + the return-edge sign `sgn det(u, edge P_ε (softNewIndex j)) = τ` (lem:soft-generic (ii), 7th conjunct) |
| SftcDirections | `sftc_dir` (def), `sftc_dir_of_ne`, `sftc_dir_att`, `sftc_dir_zero`, `sftc_continuous_dir`, `sftc_edge_softParentEdge` | the parent direction `dir_ε e`; `edge P_ε (softParentEdge j e) = dir_ε e` for every real ε |
| SftcAngles | `sftc_det_zero_left/_right`, `sftc_det_smul_self`, `sftc_regularPair_of_det_ne_zero`, `sftc_ne_zero_of_det_ne_zero_left/_right`, `sftc_signType_cases`, `sftc_det_ne_zero_of_sign`, **`sftc_principalAngle_add`**, `sftc_sub_one_ne` | transverse ⇒ regular pair; angle addition under a common sign |
| SftcMarkTurns | `sftc_markTurnAt` (def), `sftc_markTurnAt_zero`, `sftc_softOldIndex_pred`, `sftc_softOldIndex_succ_pred`, `sftc_softNewIndex_pred`, `sftc_edge_pred_old`, **`sftc_markPrincipalTurn_toMark`**, **`sftc_markPrincipalTurn_att_new`** | the explicit turn `∠(dir_ε(in m), dir_ε(out m))`; transported corners keep it; `μ_j + M_ε` merge into it |
| SftcCornerSets | `sftc_mem_cornerSet_Q`, `sftc_sum_cornerSet_Q`, `sftc_rotation_mul_two_pi` | corner marks of the transported carrier = mapped corner marks (+ `M_ε` iff through `μ_j`); `2π r_{Q_ε} = F(ε)` |
| SftcLimit | `sftc_turnSum` (def), `sftc_turnSum_zero`, `sftc_continuousAt_turnSum`, **`sftc_rotation_eventually`** | `F`, `F(0) = 2π r_q`, continuity, the uniform `δ` |
| SftcRecord | `sftc_next_map`, **`sftc_gaussList_map`**, **`sftc_gaussRecordIso`** (def), **`sftc_homfly_eq`** | `List.next` under an injective map; the literal Gauss-list transport; the record isomorphism; HOMFLY equality |

Redundancies with accepted lemmas NOT in the frozen import closure (different names, no clash; replace at port time if
the module is imported): `sftc_regularPair_of_det_ne_zero` = `regularPair_of_det_ne_zero` (SM/SoftRotation.lean:73);
`sftc_softOldIndex_pred / _succ_pred / sftc_softNewIndex_pred` = SM/SoftRotation.lean:127/133/137;
`sftc_principalAngle_smul` is not needed (`sge_principalAngle_smul`, U103-E, is used).  Duplicates of text placed AFTER
the leaf in the frozen file (hence unusable there): `sftc_signType_cases` = `sft_signType_cases` (:8035),
`sftc_sub_one_ne` = `sftb_sub_one_ne` (U112-B, :7938).  `sftc_next_map` has no Mathlib counterpart (`List.next_map`
does not exist); it is proved from U112-A's `sfta_next_eq_of_getElem`.  `sftc_soft_data` supersedes `sfta_soft_data`
(one more conjunct); the leaf uses only `sftc_soft_data`.

## 3. Statement fidelity

Nothing changed: the leaf's docstring, binders and conclusion are byte-identical (stmt_check 49/49).  The printed
sector is proved as stated, in ℤ, for all `0 < ε < ε₁` with `ε₁ = min δ₁ δ₂` (`δ₁` from lem:soft-generic's interval,
`δ₂` from the rotation continuity), quantified over every genericity proof `hQ` (FR-CC-12).  The proof does not use
the floor (as PLAN §3.4 requires: "NO floor"), nor `corner_values_i`, nor any `s7_`/`sg_` leaf.

## 4. Method note

Developed on a scratch harness (imports + the `sge_` general helpers 702-796 + the `sfta_` block 5656-7108 + the new
helpers, ≈ 2.3k lines, 16-20 s per iteration), then spliced; 5 compile iterations to 0 errors.  Reproduce the checks:
`cd work/drafts/corner && python3 tools/stmt_check.py W2_SFTC.lean && cd ../../lean && lake env lean ../drafts/corner/W2_SFTC.lean`.
For the assembler: the unit is a pure insertion at the anchor "before the docstring of `sft_same_sign`" plus the leaf
body; `python3 tools/partial_assemble.py --units …,W2_SFTC` should classify it as clean (hunks `7109a`, `7119c` relative
to Partial_Assembled.lean; relative to Statements_FINAL.lean the anchor is the same docstring).
