# W3_SKELETON_REPORT — unit U-W3-0 (skeleton architect), Wave 3 of the moves toolkit (row 177)

U-W3-0 (subagent), 2026-09-15 ≈ 21:20 UTC / 5:20pm ET.  Inputs: PLAN_FINAL.md §1c, §4.4, §5 Wave 3, §6 R2/R3;
`Port_GenericTransportSw_draft.lean` (frozen); RProof/GenericTransport.lean (`G11_Config` :111,
`G11_core_statement` :190, `G11_Params` :235–8630, `G11_exists_params` :8705, `G11_core` :8775, Unit A :8780–10261,
Unit F :10263–10942, the row :10944–11176; the positivity blocks :5570–5610, :5875–5930, :7069–7162, :7845–7880);
rlane2/NOTES_FINAL.md; RALedgers.lean (`esc_*` :1897–2060, `esc_couple` :2277, `esc_ledger` :2330);
cvtail/U_R177_REPORT.md; SM/BigonDeletion.lean (`BigonData` :46, `exists_rii_deletion` :4999,
`esc_rii_after_smoothing_of_bigons` :5313, `_weak` :5332); SM/Smoothing.lean (`StrandKind` :912, `SpliceModel`
:1466, `crossingEquiv` :3486, `toDiagram` :3626, `smoothDiagram` :6014, `smoothDiagram_record` :8155);
SM/LinkMoves.lean (`OutsideMatch` :316, `Clean` :342, `MoveMatch` :356, `RIIIData` :639, `OutsideMatch.switch` :1926,
`Clean.switch` :1948); SM/LinkRecord.lean (`Record` :309, `RecordIso` :539, `reconnect`/`smooth` :820–940);
SM/MarkedProducts.lean (`restrictCrossings` :210); CV/RecordHomfly.lean (`IsRecordIsoData` :240–300);
CV/Axioms.lean (`gausscode_polynomial` :260); RProof/Cores.lean (`IsAlternating` :490, `EdgeAB` :511,
`LocalizationData` :611, `GenericTableData` :2281, `G1.GoodRadius` :2708, `G1.extreme_iff_alternating` :3226).

## 0. Deliverables and checks

| item | result |
|---|---|
| `work/drafts/moves/Skeleton_W3.lean` | 1231 lines = the frozen draft (imports + `import SM.BigonDeletion`, `G11_ConfigSw`, its namespace block, `G11_core_sw_statement`, the leaf's STATEMENT, `esc_switch_riii_of_chain` — all byte-identical) + the W3 material (`w3a_`–`w3h_`, ≈ 1100 lines) |
| compile `cd work/lean && lake env lean ../drafts/moves/Skeleton_W3.lean` | exit 0, **0 errors**, ≈ 10 s; only cosmetic warnings (`if_pos`/`if_neg` deprecation ×14) |
| `declaration uses sorry` | **30** = the 30 sub-leaves of §2 (the frozen leaf `G11_core_sw` is now PROVED from them; `esc_switch_riii_of_chain` proved as in the draft) |
| `grep -c sorry Skeleton_W3.lean` | **30** (every occurrence is a sub-leaf body; the word appears in no docstring) |
| statement identity | `python3 work/drafts/moves/check_W3_identity.py Port_GenericTransportSw_draft.lean Skeleton_W3.lean` → the structure `G11_ConfigSw` (1206 B), the frozen `namespace G11_ConfigSw … end` block (1252 B), `G11_core_sw_statement` (1015 B), the statement of `G11_core_sw` (136 B) and `esc_switch_riii_of_chain` (694 B) are byte-IDENTICAL; imports = draft's + `SM.BigonDeletion`; exit 0 |
| `#print axioms` (scratch copy) | `G11_core_sw`, `w3e_strong_case_sw`: `[propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` (the accepted G11 footprint + the sub-leaves' `sorryAx`); the PROVED glue `w3b_homfly_switch_of_clauses`, `esc_switch_riii_of_chain`: standard + `lit_homfly`/`lp_lm` (through `homfly`, `gausscode_polynomial`); `w3b_moveMatch_switch`, `w3c_htrans_sw`, `w3e_alt_of_completeLocal`, `w3e_trans_sw_of_alt`, `w3e_configOfSw`: standard only |
| **`G11_core_sw`** | **PROVED** from `w3a_exists_params`, `w3a_exists_Ψ₀`, `w3d_exists_Ψ₁_sw` (← `w3a_exists_Ψ₁`), `w3c_riii_sw` (← `w3a_riii_param` + the six `w3a_over_*` + `w3a_y_ne`/`y'_ne`) and the PROVED switch transport `w3b_*` — the assembly `core_of_params` of the accepted G11 with the two switches carried through |
| **`w3e_strong_case_sw`** (the switched `G11_strong_case`: `homfly (D_L^{sw}) = homfly (D_H^{sw})` for the two lifts across the wall) | **PROVED** from `G11_core_sw`, `w3e_configOfSw` (defined), `w3e_xs_point`, `w3e_liftVisit_σD_sw`, `w3e_recordIsoData_sw` and `CV.gausscode_polynomial` |

Nothing under `work/lean` was written or read-modified.

## 1. Pre-review verdict

### 1.1 The structural finding: "Units B–D verbatim" is impossible — `G11_Config.trans` is in the TYPE of everything

PLAN §5 Wave 3 and the draft's docstring assume the accepted shadow-level material (`X₀`, `X₁`, `M₀`, `M₁`, the
disc, the arcs, the move match, `exists_Ψ₀`, the E-key comparison …) is reused verbatim and only D8/E/F are
re-derived.  **This is false.**  Every one of the 1056 declarations of `namespace RProof.G11_Params`
(GenericTransport 235–8630) is stated for `π : G11_Params C` with `C : G11_Config k`, and
`G11_Config.trans : ¬ IsAlternating (crossingSign X m p) (crossingSign X m q) (crossingSign X p q)` is FALSE on the
K3 side of row 177 (the over-order of the positive lift is cyclic — `GenericTableData.extreme_iff_alternating`:
`ExtremeLocal ↔ IsAlternating`; that is exactly why the printed proof switches `x` first).  So for a 177
configuration NO term `C : G11_Config k` exists, and no accepted `π.…` lemma can be applied — although none of
their proofs uses `trans` (grep: `C.trans` appears only at :7102/:7109 inside `gu6_htrans`, which is consumed only by
`riii` :7440).  Lean cannot strip a hypothesis from a compiled theorem; the only escape routes are (i) editing the
accepted `G11_Config` (FORBIDDEN: accepted declarations are never rewritten), or (ii) the ADDITIVE alternative —
a trans-free copy.  The skeleton takes (ii): `G11_ParamsSw (C : G11_ConfigSw k)` (the fields of `G11_Params`
verbatim; no field mentions `trans`) and states as sub-leaves exactly the facts about it that the switched instance
needs (§2 unit (a)); their proofs are the accepted proofs with `G11_Config → G11_ConfigSw` (mechanical).

Measured (this unit, grep/awk on 235–8630): 1056 declarations; **908 depend on `π`/`C` (6185 lines) and must be
re-derived** for `G11_ParamsSw`; 148 are `C`-free helpers (2211 lines: `gu3_adjacent_natCast_iff`, `gu3_pt_ext`,
`gu3_visitIso_of_reparam`, `gu3_overBit_pair`, `gu6_sv_fst_eq`, `gu6_overStrand_eq`, `gu6_over_under_of_pos/neg`,
`gu6_riii_build`, `gu6_riii_of_strands`, the `GU6Single` sections, …) and are REUSED as `RProof.G11_Params.gu*`
(the skeleton already uses `gu6_sv_fst_eq`, `gu6_det_ne_zero_single`).  Also to copy: `G11_exists_params` :8705
(75 lines) and the `C`-dependent Block-F helpers :8632–8778 (`gu3_exists_small`, `gu3_triangle_compact`, … ≈ 100
lines), `G11_centroid`/`G11_discOf` (done here as `G11_centroidSw`/`G11_discOfSw`).

### 1.2 Positivity footprint (the question PLAN §6 R2 asked)

Lines of 235–8630 that MENTION a positivity-specific lemma (`positiveDiagram_det_pos/sign/isPositive`,
`gu3_overBit_pair`, `gu3_isOver_iff_det_pos`, `gu6_overStrand_eq`, `gu6_over_under_of_pos/neg`, `gu6_ov_*`,
`gu6_overBit_iff_det`, `gu6_Rmp_iff`…, `X₁_sign_*`, `crossingSign`, `IsAlternating`, `gu6_htrans`, `C.trans`):
**106** — 24 in Units B–D (the `exists_Ψ₀` over-bit identification :1451–1483 and `gu5_moveMatch`'s over data
:4451/:4454), **70 in D8** (:7069–7162 the six-case over/under table and `gu6_htrans`; :7274–7343 its use in `riii`),
6 in E (`gu6_Ψ₁_sign` :7852, `gu6_overBit_iff_det`/`gu6_Ψ₁_overBit` :7858–8009).  Consistent with the plan's
"37 + 57".  BUT these lines are NOT the cost driver: the switched instance needs the POSITIVE `M₀`, `M₁` (the
skeleton's `M₀ := positiveDiagram X₀`, `M₁ := positiveDiagram X₁`) and switches ONE crossing on each side, so every
positivity lemma is used unchanged for the positive pair and the switch is carried by the PROVED `w3b_*` transport.
Only `riii` (271 lines) changes shape: its over/under table `hov_*` becomes the hypotheses of the parametrised
`w3a_riii_param` and `gu6_htrans` becomes `htrans`.  Positivity is therefore NOT woven into G11 in any way that
costs re-derivation; the `trans` FIELD is.

### 1.3 Honest size estimate for Wave 3 (`G11_core_sw` + row-level assembly + the 177 (6) material)

| unit | content | lines | prover-hours | note |
|---|---|---|---|---|
| (a) copy | `G11_ParamsSw` re-derivation of the 908 `π/C`-dependent declarations of 235–8630 (Units B–D, D8 as `w3a_riii_param`, E as `w3a_exists_Ψ₁`), `G11_exists_params`, Block F | **≈ 6.4k** (mechanical) | 25–40 | the 148 `C`-free helpers are reused; `riii` re-typed (+30 lines), `gu6_htrans` dropped |
| (a) new | the 21 `w3a_*` sub-leaf bodies as CONNECTORS to the copy (each is one accepted lemma renamed; `w3a_exists_Ψ₀/Ψ₁` add the crossing-correspondence clauses: `gu6_sv_fst_eq`, `gu6_svisit_ext`, `gu3_remote_*`) | 0.3k | 6 | |
| (b) | switch transport | **DONE** (PROVED here; optional `w3b_reparam_switch` 0.15k) | 0–4 | |
| (c) | D8′ | **DONE** (PROVED here) | 0 | |
| (d) | E′ | **DONE** (PROVED here) | 0 | |
| (e) | `w3e_xs_point` (0.15k), `w3e_liftVisit_σD_sw` + a `halt`-free `gu6_lift_six` (0.25k), `w3e_recordIsoData_sw` (0.3–0.5k: copy :10852–10920 with the switched bits) | 0.7–0.9k | 12–18 | `w3e_configOfSw`, `w3e_cfg_trans_sw`, `w3e_alt_*`, `w3e_strong_case_sw` DONE |
| (g) | the two `j = 2` sites `w3g_*` | 2.0–2.4k | 30–40 | the second can be derived from the first through `Diagram.reverse`? (not checked; stated separately) |
| (h) | `w3h_record_core` 1.2k, `w3h_smooth_record_occ` 0.2k, `w3h_restrict_switch_deleted` 0.06k, `w3h_hrec` 0.4k | 1.9k | 30–40 | |
| skeleton | this file | 1.2k | — | |
| **total** | | **≈ 12.5–13k lines, of which ≈ 6.4k mechanical copy; ≈ 6k genuinely new** | **≈ 105–140 h** | |

**Verdict: PLAN §5's "≤ 8–10k lines" is NOT realistic as a line count (≈ 12.5–13k), but its hour estimate
(105–140 h) IS: the excess is the mechanical `G11_ParamsSw` copy, cheap in hours and expensive in compile time.**
PLAN §6 R2's premise ("re-derivation is local, 4.5k, IF the refactor makes D8/E take the over bits as a
parameter") fails on the `trans` field, not on positivity; the plan's fallback ("6–7k if B–D's `positiveDiagram`
naming must be generalised") is closer but still undercounts the copy.  The parametrised D8 (`w3a_riii_param`)
is exactly DESIGN_A's process graft and is stated here; its positive instance is the accepted `riii`.

### 1.4 Is `trans_sw` extractable from `CompleteLocal` at the K3 side?  Yes, but NOT from `esc_interface`'s hypotheses

`w3e_alt_of_completeLocal` (PROVED): `CompleteLocal → ExtremeLocal` (`extremeLocal_iff`, `Or.inl`) and
`GenericTableData.extreme_iff_alternating` give `IsAlternating (strandSign e f) (strandSign e g) (strandSign f g)`;
`w3e_trans_sw_of_alt` (PROVED by `decide`; needs the sign `≠ 0`, see §5) flips the `sw` entry; `w3e_cfg_trans_sw`
(PROVED, the copy of `G11_cfg_trans` :10040) carries it to the configuration's `crossingSign` triple via
`G11_carrierSign`.  So `w3e_configOfSw` extracts a `G11_ConfigSw` from the same inputs as `G11_configOf` (minus
`halt`) plus `sw` and the flipped strand-sign clause.  **However** the alternation needs `GenericTableData E e f g δ`
(or `G1.GoodRadius`: `G1.extreme_iff_alternating h3 hδ` :3226), and `hdet` (the det signs agree across the wall, needed
by F′ and by every wall record iso) needs `AV_EventRadius E δ` (`hR.sign_eq` + `GT_det_pos_iff_of_sign`, as in
`G11_empty_groupedPoly_eq` :11074).  The FROZEN `esc_interface` (RALedgers :2027) passes only
`LocalizationData` (crossing sets, orders, interlacement — no sign data: checked field by field, Cores :611–700).
Row 173's assembly had both `hGT` (from `generic_table … hE`) and `hR`.  **Executor decision F-177-2 (interface
edit, D-F11-internal like F-177-1): add `(hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)` to
`esc_interface`'s hypotheses; `esc_couple` (:2277) has `hE`, `hR` and can obtain `hGT` by `generic_table E e f g h3
h4e h4f h4g hE` + `SEL_genericTableData_mono` exactly as `generic_transport` :11158 does (≈ 10 lines).**  Without it
the realiser of `switch_riii` (and of `rii_after_smoothing`'s wall bijection) has no `hdet`.

## 2. The API and the sub-leaf list (names and line numbers in Skeleton_W3.lean)

### 2.0 Additive `G11_ConfigSw` API (namespace `SM.Link.G11_ConfigSw`, all PROVED) — lines 121–207
`D₀` (:127, the UNSWITCHED positive diagram; `D₀sw_eq_switch : D₀sw = D₀.switch xs := rfl` :129),
`x_mp x_mq x_pq : D₀.Γ.Crossing` (:134–136), `xs_eq : xs = if sw = 0 then x_mp else if sw = 1 then x_mq else x_pq`
(:139), the six occurrences `v_mp … v_qp : D₀.Γ.Visit` (:148–153) with `v_*_fst` (:155–160), `clear_edge` (:163,
copy of `G11_Config.clear_edge`), `det_mp_ne/mq/pq` (:171–176), the switched over relations
`Rmp_sw := (0 < det (edge X m) (edge X p)) ↔ sw ≠ 0` etc. (:180–182), **`w3c_htrans_sw`** (:186, PROVED: `trans_sw` in
the `gu6_htrans` form consumed by the parametrised D8).

### 2.1 Unit (b) switch transport (section `W3Switch`, lines 210–341) — PROVED except the optional leaf
`w3b_visitBetween_switch` (`Iff.rfl`), `w3b_twin_switch` (`rfl`), `w3b_componentCount_switch` (`rfl`),
`w3b_fst_eq_iff_of_twin` (:219, crossing correspondence of a twin-preserving bijection),
`w3b_overBit_switch_of_visitIso` (:234), `w3b_sign_switch_of_visitIso` (:242), `w3b_isRecordIsoData_of_clauses`
(:252), `w3b_homfly_of_clauses` (:263, `ax:gausscode` from the four clauses), **`w3b_homfly_switch_of_clauses`**
(:276, the record-level replacement of PLAN (b): `homfly (D.switch x) = homfly (D'.switch x')` from a visit
bijection matching `x ↦ x'`), `w3b_isRecordIsoData_switch` (:287), `w3b_outsideMatch_switch_right` (:299, mirror of
the accepted `OutsideMatch.switch`), **`w3b_moveMatch_switch`** (:320), `w3b_localFrame_switch` (:328).
Sub-leaf: **`w3b_reparam_switch`** (:339, sorry :341) — OPTIONAL, not on the assembly's path.

### 2.2 Unit (a) the trans-free parameter structure (lines 350–615, 792) — 21 sub-leaves
`G11_centroidSw` (:350), `G11_discOfSw` (:354), `structure G11_ParamsSw` (:359, the fields of `G11_Params`);
namespace `G11_ParamsSw`: `hk₃ X₀ mid mA mB mC mD p' q' apex X₁ U comp₀ comp₁` (:384–408), `M₀ M₁` (:421–422),
`st₀ st₁` (:428–429, the strand `⟨0, i⟩`), the local crossings `y_mp y_mq y_pq y'_pC y'_qB y'_pq` (:448–453), the
twelve local occurrences `w_mp … w'_qp` (:457–479) with `*_fst` (:482–493), `x₀ x₁` (:497–498, the switched
crossing on each side, by `sw`), `M₀sw M₁sw` (:501–502, `abbrev`).
| sub-leaf | line (sorry) | accepted source to copy |
|---|---|---|
| `w3a_X₀_generic` | 412 (413) | `X₀_generic` :857 + U3 Block A |
| `w3a_X₁_generic` | 417 (418) | `X₁_generic` :2858 + U4 :2708–2850 |
| `w3a_X₀_cross_mp/mq/pq` | 434/436/438 | `X₀_cross_*` :949–969 |
| `w3a_X₁_cross_pC/qB/pq` | 440/442/444 | `X₁_cross_*` :2869–3380 |
| `w3a_y_ne`, `w3a_y'_ne` | 509, 511 | `gu6_y_*_ne_*` :7016–7044 |
| `w3a_over_mp₀/mq₀/pq₀` | 518/524/530 | `gu6_ov_*` :7115–7136 via `gu6_Rmp_iff` :7069, read on strands (`gu6_over_under_of_pos/neg` :5879) |
| `w3a_over_mp₁/mq₁/pq₁` | 536/542/548 | `gu6_ov_pC/qB/pq'_*` :7139–7162 via `gu6_R_pC_iff`/`gu6_R_qB_iff` :7079–7087 |
| `w3a_exists_Ψ₀` | 560 (569) | `exists_Ψ₀` :1403 (B4) + crossing correspondence (`gu6_sv_fst_eq`, `gu3_visit_ext`) |
| **`w3a_riii_param`** | 582 (595) | `riii` :7172–7441 re-typed for `withOver f₀ hf₀`/`withOver f₁ hf₁`; `hov_*` := the six hypotheses; `gu6_htrans` := `htrans`; frame/match via `⟨h.frontier_injOn, h.exits⟩`, `gu5_moveMatch` with `over_eq` from `h₀ h₁` + `inner_M₀/₁` |
| `w3a_exists_Ψ₁` | 603 (615) | `exists_Ψ₁` :8552 (E1) + the three crossing-correspondence clauses from `gu6_Ψ₁_w_*` :7786–7810 |
| `w3a_exists_params` | 792 (793) | `G11_exists_params` :8705 with `G11_ConfigSw.clear_edge` |

### 2.3 Unit (c) D8′ (lines 620–742) — PROVED
`sw_cases`, `x₀_eq0/1/2`, `x₁_eq0/1/2`, `x₀_cases`, `x₁_cases`, `x₀_eq_mp/mq/pq_iff`, `x₁_eq_pC/qB/pq_iff` (:620–689),
`w3c_table_aux` (:693, the generic local table: switching `x` flips the over strand at `y` iff `x = y`),
**`w3c_riii_sw : RIII M₀sw M₁sw`** (:723), `w3c_homfly_M₁sw` (:741).

### 2.4 Unit (d) E′ (lines 748–790) — PROVED
`x₁_iff_of_local` (:748), `x₀_iff_of_local` (:759), **`w3d_exists_Ψ₁_sw`** (:772: `Ψ₁ : M₀.Γ.Visit ≃ M₁.Γ.Visit` with
twins, over bits, signs on `M₀sw/M₁sw` and the `σD`-twisted cyclic order).

### 2.5 The leaf (line 796) — PROVED
`G11_core_sw` (:796–813): `D₁ := M₁sw`, `Ψ := Ψ₀.trans Ψ₁`, homfly by `w3c_homfly_M₁sw` and
`w3b_homfly_switch_of_clauses` (the `D₀sw ≅ M₀sw` step at the record level), the four clauses by `exact` terms.

### 2.6 Unit (e) A′ + F′ + the row-level assembly (section `W3E`, lines 815–1073) — 3 sub-leaves
`w3e_alt_flip` (:829, PROVED, `decide`), `w3e_trans_sw_of_alt` (:837, PROVED), **`w3e_alt_of_completeLocal`** (:848,
PROVED), `w3e_swPair` (:862), **`w3e_cfg_trans_sw`** (:869, PROVED), **`w3e_configOfSw`** (:897, DEFINED — the twelve
accepted Unit-A leaves + `sw`, `trans_sw`), `w3e_configOfSw_D₀sw` (:924, `rfl`),
| sub-leaf | line (sorry) | source |
|---|---|---|
| `w3e_xs_point` | 943 (956) | `gu3_crossingPoint_symm` + `G11_carrierEdge_crossingPoint` :8976, three cases on `sw` |
| `w3e_liftVisit_σD_sw` | 960 (974) | `G11_liftVisit_σD` :10793 + a `halt`-free `gu6_lift_six` |
| `w3e_recordIsoData_sw` | 986 (1007) | `G11_recordIsoData` :10852–10920 with the switched bits (see its docstring) |
**`w3e_strong_case_sw`** (:1017, PROVED): the switched `G11_strong_case`.

### 2.7 Row 177 (6) (section `Row177_6`, lines 1075–1229) — 6 sub-leaves (statements + sketches)
`w3g_bigonData_smooth_arcST` (:1086, sorry :1103), `w3g_bigonData_smooth_arcTS` (:1113, :1130),
`w3h_record_core` (:1146, :1161), `w3h_smooth_record_occ` (:1170, :1174), `w3h_restrict_switch_deleted` (:1180, :1183),
`w3h_hrec` (:1198, :1224 — the consumer's `hrec` for `esc_rii_after_smoothing_of_bigons`).

## 3. Design decisions (what the executor should NOT re-litigate)

1. **The over data are carried by the POSITIVE `M₀`, `M₁` plus one switch per side**, never by a generalised
   positive lift: `M₀sw := M₀.switch x₀`, `M₁sw := M₁.switch x₁` with `x₀ ∈ {y_mp, y_mq, y_pq}`, `x₁ ∈ {y'_pC, y'_qB,
   y'_pq}` selected by `sw` (the pair `{m,p}` becomes `{p', mC}` after the move: `gu6_Ψ₁_w_mp : Ψ₁ w_mp = w'_Cp`).
   Every shadow-level fact is then literally the accepted one; only the over/under table of `riii` is parametrised.
2. **The parametrised D8 `w3a_riii_param`** takes arbitrary `f₀ f₁` positive off the three local crossings, three
   Props `Rmp Rmq Rpq` ("`m` over `p`" etc. — the "six local over bits" of PLAN (a), one Prop per pair, the two bits
   of a pair being complementary), the local tables in the `gu6_riii_of_strands` implication form, and `htrans`.
   The positive instance (`f₀ := M₀.overStrand`, `Rmp := 0 < det (edge X m) (edge X p)`, `htrans := gu6_htrans`) IS
   the accepted `riii`; the switched instance is `w3c_riii_sw` (PROVED here through `w3c_table_aux`).
3. **The homfly step `D₀sw → M₀sw` is at the record level** (`w3b_homfly_switch_of_clauses`: `Ψ₀`'s four clauses +
   `CV.recordIsoOfData` + `ax:gausscode`), not through the five `Reparam`s: no crossing has to be tracked through
   five reparametrizations, and `gausscode_polynomial` is already in the row's footprint (G11 Unit F).  PLAN (b)'s
   `Reparam D D' → Reparam (D.switch x) (D'.switch x')` is stated as the optional `w3b_reparam_switch` for fidelity.
4. **`w3a_exists_Ψ₀`/`w3a_exists_Ψ₁` carry crossing-correspondence clauses** (`∀ v, (Ψ v).1 = y' ↔ v.1 = y`) so that
   the switch transport needs no label arithmetic in the assembly; the executor proves them from the six visit
   images + `gu6_sv_fst_eq` + `Diagram.eq_or_eq_twin` (or `w3b_fst_eq_iff_of_twin`).
5. **The K3 configuration is extracted with `sw` as a parameter** (`w3e_configOfSw … sw hsw`): the consumer passes
   `sw := 0` (`x = x_ef`) in the main case `hord : t(x_ef) < t(x_eg)` and `sw := 1` after the relabelling `f ↔ g`
   (`G11_exact_swap`, `G11_isCrossing_comm`, `G11_triangleCrossings_swap`, `G11_param_ne`), exactly as
   `GT_G11_strong_proof` :10989 does; `x_H, x_L` are identified by their double points (`w3e_swPair`,
   `crossingTransport`) as `esc_MoveData.switch_riii` names them.
6. **Row 177 (6)** is stated for `toDiagram D x M hε` (any `SpliceModel`) so that one statement serves the self and
   mixed models (`smoothDiagram` is `toDiagram (selfModel …)`/`(mixedModel …)` after `unfold; split_ifs`); the
   orientation caveat is the two theorems `arcST`/`arcTS`; the record lemma is split into the pure record core
   (`w3h_record_core`, twisted-successor form `Φ (σ (s (σ v))) = s' (Φ v)`), the exposed record bridge
   (`w3h_smooth_record_occ`, needed because the accepted `smoothDiagram_record` is a bare `Nonempty`), the
   deleted-switch companion and the consumer-form composite `w3h_hrec`.

## 4. Executor decisions and open points

* **D1 — the copy (accepted module frozen).**  The `G11_ParamsSw` re-derivation (≈ 6.4k lines) must live in a NEW
  module (proposed `RProof/GenericTransportSw.lean`, or two — `…SwBC.lean` for Units B–C ≈ 3.5k and
  `…SwDE.lean` for D/D8/E ≈ 3k — to keep the per-check compile time under control; the accepted G11 file takes
  minutes).  It is `sed`-mechanical: `G11_Config → G11_ConfigSw`, `G11_Params → G11_ParamsSw`, `G11_discOf →
  G11_discOfSw`, keep every `gu*` name inside the new namespace (no clash: different namespace), delete
  `gu6_htrans`, re-type `riii` as `w3a_riii_param`.  Alternative (NOT recommended, forbidden as stated): edit
  `G11_Config` to drop `trans` into `G11_Params`/`riii` — statement-neutral for the row but a rewrite of an accepted
  declaration.  If the lane owner grants an exception, Wave 3 shrinks to ≈ 4k lines.
* **D2 — F-177-2 (interface edit):** add `GenericTableData` and `AV_EventRadius` to `esc_interface` (§1.4).  Also
  needed by the realiser from the ledger side: `hX` (`hL.gauss_words`), `hcarr` (`GT_geoCarrierCrossings_eq_of_good`
  of `GT_empty_wall`, which needs `hR` as well), `htri` (`GT_empty_tri_subset`), all available in `esc_couple`.
* **D3 — the nonzero sign** for `w3e_trans_sw_of_alt` (`strandSign (E.curve t) e f ≠ 0`): from
  `strandSign_eq_crossingSign` + genericity of `E.curve t` (`genericAt`), or `G1.signs_ne_zero` with `GoodRadius`.
* **D4 — the orientation caveat of (6):** the realiser must show that the triangle's corner at `x` is cut by the
  ORIENTED smoothing, i.e. `(y before x on s ∧ z after x on t) ∨ (y after x on s ∧ z before x on t)`; in the two
  other combinations no bigon exists after smoothing (the printed proof asserts the bigon, so the 177 sign table must
  imply the coherent case — to be derived, e.g. from `GenericTableData` (1c) `s_o = −σ` or R-LOC (2)'s adjacency and
  the extreme orbit; not checked here).
* **D5 — `same_over` for the (6) sites:** the hypothesis `hover : D.overStrand y = g ↔ D.overStrand z ≠ g` (exactly one
  of `y, z` has `g` over on the positive lift) is the printed sign table (cyclic order on K3: `g` over `e` at `y`,
  `f` over `g` at `z`); on the empty side the same triple (`hdet`).  To be supplied by the realiser.
* **D6 — the wall bijection for `w3h_hrec`** (`Ψ` with the σ-twisted `VisitBetween`) is G11 Unit F's
  `G11_twisted_key_lt` + `visitTransport` applied to the two lifts — the realiser can reuse `G11_recordIsoData`'s proof
  body (:10852–10920) or the strong form suggested in `w3e_recordIsoData_sw`'s docstring.

## 5. Pitfalls met (Lean 4 v4.34.0-rc2 / this Mathlib)

* `decide` REFUTED my first `w3e_alt_flip`: `IsAlternating 0 0 0` (`a = c ∧ b = -a`) holds and is flip-invariant, so
  the flip lemmas need `a ≠ 0` — a real content point, not a Lean quirk (SignType has `0`).
* `⟨0, i⟩ : π.M₀.Γ.Strand` fails (`OfNat (Fin π.M₀.Γ.c) 0`: `c` does not reduce through `M₀`); write
  `(⟨0, i⟩ : (Shadow.single π.comp₀).Strand)` (the accepted file's pattern) — hence `st₀`, `st₁`.
* `if … then … else …` on `Fin 3` conditions: `if_true`/`if_pos h`-as-simp-lemma do not fire across the instance
  produced by `unfold`; full `simp [h0]` (the `reduceIte` simproc) or `rw [if_pos h]` do.  `if_pos`/`if_neg` are
  deprecated in favour of `ite_eq_left/right` (warnings only).
* `if y = π.x₀` in a STATEMENT needs `DecidableEq π.M₀.Γ.Crossing` (absent): state such facts as two lemmas or use
  `Classical`; I removed them.
* A `def M₀sw := M₀.switch x₀` blocks `rw`/`simp` ("not type-correct under `implicit` transparency" when a
  `M₀.Γ.Crossing` meets `M₀sw.Γ.Crossing`); `abbrev` fixes the abbreviation layer, and the `switch` layer is handled
  by stating the E′ bijection on the UNSWITCHED visit types (`Ψ₁ : M₀.Γ.Visit ≃ M₁.Γ.Visit`) and closing the
  assembly's goals with `exact` terms (defeq at default transparency) instead of `simp only [Equiv.trans_apply]`.
* `Clean U D`, `LocalFrame`, `MoveMatch` are structure TYPES indexed by `D`: `Clean U M₀` is not `Clean U (M₀.withOver
  f h)`; rebuild by fields (`⟨h.frontier_injOn, h.exits⟩`, as `Clean.switch` does) — relevant for `w3a_riii_param`.
* `variable (π : G11_ParamsSw C)` + an explicit `(_π : G11_ParamsSw C)` parameter gives a TWO-`π` declaration and
  breaks `π.foo` field notation on everything downstream ("does not have a usable parameter of type …").
* `omit`/`include`: theorems in `namespace G11_ParamsSw` that mention only `C` need `C` explicit or must live in
  `namespace G11_ConfigSw` (done: `w3c_htrans_sw`, `sw_cases`).

## 6. Recommended unit prompts (Wave 3 executor; parallelisable as marked)

* **W3-A1 (the copy, 2 provers in parallel):** "Create `work/drafts/moves/W3_A1_BC.lean` = Skeleton_W3.lean's prefix
  through `end G11_ConfigSw` (line 207) + a verbatim copy of GenericTransport.lean 235–4917 with `G11_Config →
  G11_ConfigSw`, `G11_Params → G11_ParamsSw`, `G11_discOf → G11_discOfSw`, `C.clear_edge → C.clear_edge` (the skeleton's),
  reusing every `C`-free `RProof.G11_Params.gu*` by qualified name instead of copying it; 0 errors; close
  `w3a_X₀_generic`, `w3a_X₁_generic`, the six `w3a_X*_cross_*`, `w3a_y_ne`, `w3a_y'_ne`, `w3a_exists_Ψ₀`, the six
  `w3a_over_*`, `w3a_exists_params`."  Second prover: lines 4918–8630 (D, D8 → `w3a_riii_param`, E → `w3a_exists_Ψ₁`).
  Statement-identity: the 21 `w3a_*` statements of the skeleton, byte-identical.
* **W3-E (after A1, or in parallel on `sorry`'d A1):** "Close `w3e_xs_point`, `w3e_liftVisit_σD_sw`,
  `w3e_recordIsoData_sw` (copy `G11_liftVisit_σD` :10793 with a `halt`-free `gu6_lift_six`; copy `G11_recordIsoData`
  :10852–10920 exposing `Φ = Ψ.symm.trans Λ` and flip the bits at `x, x'` with `w3b_*`)."
* **W3-G (parallel):** "`w3g_bigonData_smooth_arcST`, then `arcTS` (try `Diagram.reverse`/the mirror to derive one
  from the other; else copy); template BigonDeletion §2a (`exists_bigonData_of_triangle`) and Smoothing §3–§6."
* **W3-H (parallel):** "`w3h_restrict_switch_deleted` (60 lines), `w3h_smooth_record_occ` (unfold
  `selfRecordIso`/`mixedRecordIso`), `w3h_record_core` (the eight orientation patterns; `firstReturn` toolbox of
  LinkRecord/Smoothing §8), then `w3h_hrec`."
* **W3-I (ledger side, after F-177-2):** realise `esc_MoveData.switch_riii` from `w3e_strong_case_sw` with
  `carrierDiagram = geoPositiveLift` (`unfold CV.carrierDiagram`), the relabelling case split as in
  `GT_G11_strong_proof`, `w3e_alt_of_completeLocal`, `w3e_trans_sw_of_alt`; and `rii_after_smoothing` (weak form
  `esc_rii_after_smoothing_weak`) from `w3g_*` + `w3h_hrec` + `esc_rii_after_smoothing_of_bigons`.
