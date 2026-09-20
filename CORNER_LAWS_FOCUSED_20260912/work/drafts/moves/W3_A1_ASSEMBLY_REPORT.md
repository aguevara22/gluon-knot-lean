# W3_A1_ASSEMBLY_REPORT — assembly of the row-177 Wave-3 trans-free copy (unit W3-A1, BC + DE)

Assembler (subagent), 2026-09-15 21:46–21:55 UTC / 5:46–5:55pm ET (bounded test, audit A-177-1; hard stop
00:30 UTC not approached).  Inputs: `Skeleton_W3.lean` (1231 lines, 30 `sorry`), `W3_A1_BC.lean` (5161 lines) +
`W3_A1_BC_REPORT.md`, `W3_A1_DE.lean` (3968 lines) + `W3_A1_DE_REPORT.md`, `check_W3_identity.py`,
`Port_GenericTransportSw_draft.lean` (the frozen statements).  Compile command throughout:
`cd work/lean && lake env lean ../drafts/moves/<file>.lean` (Lean 4.34.0-rc2 toolchain of `work/lean`).
Nothing under `work/lean` was written; no `lake build`.

## 0. Result — the test's success criterion

**The trans-free copy is complete and compiles: `W3_A1_Assembled.lean`, 7827 lines, 1096 declarations, exit 0,
0 errors, 36 s; every one of the 20 `w3a_*` sub-leaves is closed; the Wave-3 leaf `G11_core_sw` and the row
theorem `esc_switch_riii_of_chain` are `sorryAx`-FREE (`#print axioms`: standard axioms + the three registered
literature axioms `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` only).**  The 10 remaining `sorry` bodies are
exactly the expected Wave-3b sub-leaves (3 × `w3e_`, 2 × `w3g_`, 4 × `w3h_`) plus the optional `w3b_reparam_switch`.

| item | result |
|---|---|
| **`work/drafts/moves/W3_A1_Assembled.lean`** | **7827 lines**, 1096 declarations (regex count): skeleton material + BC copy 512 (`section W3A1Copy`, lines 241–3951) + DE block 427 (`section W3DECopy`, lines 4193–6846: 393 copied + 34 new `w3de_`) + 4 `w3bc_` helpers |
| compile | **exit 0, 0 errors**, 36 s wall (74 s CPU); warnings: **10 × `declaration uses sorry`** (§3) + 14 cosmetic `if_pos`/`if_neg` deprecations inherited from the skeleton (lines 4001–4002, 7101–7110) |
| `grep -c '^  sorry'` | skeleton **30 → 10** (BC closed 18, DE closed 2; nothing else changed) |
| `#print axioms` (scratch copy, §4) | `G11_core_sw`, `esc_switch_riii_of_chain`: **no `sorryAx`**; all 20 `w3a_*`, `w3de_riii_param`, `w3de_exists_Ψ₁`, `w3c_riii_sw`, `w3d_exists_Ψ₁_sw`: `[propext, Classical.choice, Quot.sound]`; `w3e_strong_case_sw`: `sorryAx` through the three `w3e_` sub-leaves only |
| statement identity (§2) | `check_W3_identity.py Port_GenericTransportSw_draft.lean W3_A1_Assembled.lean`: the 5 frozen blocks **IDENTICAL**, imports OK, exit 0; `check_W3_statements.py`: **42/42** `w3a_…w3h_` statements (from `theorem` to `:= by`) byte-identical to the skeleton, **20/20** `w3a_`; every skeleton declaration name still declared; the moved block `G11_centroidSw`/`G11_discOfSw`/`structure G11_ParamsSw` (skeleton 345–379) byte-identical |
| name clashes against `work/lean` (§5) | **0** fully-qualified clashes among 1096 declarations; 925 informational short-name coincidences (the copy mirrors `RProof.G11_Params` name for name, in the namespace `SM.Link.G11_ParamsSw`) |
| de-duplication (§1) | 19 declarations of `W3_A1_DE.lean` dropped (8 aliases + 11 black boxes), replaced by BC's proved copies; 0 internal duplicates remain |
| scripts | `assemble_W3.py` (regenerates the file from the two unit files: `python3 assemble_W3.py` in this directory), `check_W3_statements.py <file>`, `clash_scan_W3.py <work/lean> <file>` |

## 1. Assembly (how the two copies were joined)

Base = `W3_A1_BC.lean` (which is the skeleton with the BC copy inserted after `end G11_ConfigSw`, the
`G11_ParamsSw` structure block moved up in front of it, the 18 BC sub-leaves closed, and the skeleton's duplicated
definitions `hk₃ X₀ mid mA mB mC mD p' q' apex X₁ U M₀ M₁ *_componentCount w_*` removed in favour of the copy's).
Into it, immediately after `theorem M₁sw_componentCount` (BC line 4181 = the DE prover's insertion point "after
skeleton line 506") went the DE block: `W3_A1_DE.lean` lines 508–523 (the `/-! ### W3-A1-DE` header, `section
W3DECopy`, the two `open`s, `variable {n}`) and 596–3242 (`/-! #### The copy proper` … `end W3DECopy`).  Omitted:
DE lines 524–595 = the 8 alias theorems `X₀_generic X₁_generic X₀_cross_mp/mq/pq X₁_cross_pC/qB/pq` (bodies
`π.w3a_…`) and the 11 black boxes `X₁_cross_iff X₁_sign_pC X₁_sign_qB disc_isDisc triangle_sub_interior inner_M₀
inner_M₁ clean_M₀ clean_M₁ exists_moveMatch exists_arcCovers` (bodies `sorry`) — exactly the 19 names the two blocks
had in common (`DE ∩ BC-copy` = these 19, `DE ∩ BC-rest` = ∅, no duplicate inside either block, no name of either
`open RProof.G11_Params (…)` list is declared by the other block).  BC's copies of the 19 are the accepted
statements verbatim (typed over the literal `⟨k + 3, π.hk₃, π.X₀⟩`), which is what the DE copy was elaborated against
through its aliases, so the DE block compiled unchanged: **0 edits to any proof, 0 errors at the first compile.**
The two DE connectors were closed by their one-line bodies: `w3a_riii_param := by exact π.w3de_riii_param f₀ hf₀ f₁
hf₁ h₀ h₁ Rmp Rmq Rpq hmp₀ hmq₀ hpq₀ hmp₁ hmq₁ hpq₁ htrans` and `w3a_exists_Ψ₁ := by exact π.w3de_exists_Ψ₁ Ψ₀ h₀
hmp hpm hmq hqm hpq hqp`.  The DE header comment's last sentence was reworded to say the aliases/black boxes are
gone (no other text change).

Dependency order in the file: `G11_ConfigSw` (frozen) → additive `G11_ConfigSw` API → `G11_centroidSw`,
`G11_discOfSw`, `structure G11_ParamsSw` (moved up, verbatim) → `section W3A1Copy` (BC copy: Units B–C and D1–D7,
i.e. accepted 262–4917) → `section W3Switch` (unit (b)) → `namespace G11_ParamsSw` skeleton part (`comp₀ comp₁`,
the 8 `w3a_X*` connectors, `st₀ st₁ y_* w'_* *_fst x₀ x₁ M₀sw M₁sw`) → `section W3DECopy` (DE copy: D8, E, i.e.
accepted 4918–8629, + the `w3de_` transport) → `w3bc_` helpers → the 12 remaining `w3a_` connectors → D8′, E′ →
`w3bc_exists_small`, `w3a_exists_params` → the leaf `G11_core_sw` → `section W3E` → `esc_switch_riii_of_chain` →
`section Row177_6`.

Diff of the skeleton against the assembled file (`difflib`, line level): the only skeleton lines not present in
place are (i) 345–379 (moved up verbatim, see §2), (ii) 383–405, 420–425, 455–468 (the definitions now supplied
by the copy — `hk₃ … U`, `M₀ M₁ M₀/M₁_componentCount`, `w_mp … w_qp`; the copy's versions are the accepted text,
definitionally the skeleton's — `M₀ := positiveDiagram π.X₀_generic` vs `π.w3a_X₀_generic` is proof-irrelevant,
`⟨k + 3, π.hk₃, π.X₀⟩` vs `π.comp₀` unfolds), and (iii) the 21 replaced `  sorry` lines (20 `w3a_` + `w3a_exists_params`).
Three insert blocks: after skeleton 199 (asm 200–3952: moved block + BC copy), after 506 (asm 4183–6882: DE block +
`w3bc_` helpers), after 788 (asm 7266–7318: `w3bc_exists_small`).

## 2. Statement identity

* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3_A1_Assembled.lean` → `structure G11_ConfigSw`
  IDENTICAL (1206 bytes), `namespace G11_ConfigSw block` IDENTICAL (1252), `def G11_core_sw_statement` IDENTICAL
  (1015), `theorem G11_core_sw (statement)` IDENTICAL (136), `theorem esc_switch_riii_of_chain` IDENTICAL (694, incl.
  body), imports = draft's + `SM.BigonDeletion`: True; exit 0.
* `check_W3_statements.py W3_A1_Assembled.lean`: 42 `w3[a-h]_` statements in the skeleton, 42 in the file, 42
  byte-identical (`theorem … := by\n`), 0 differing/missing.  **The skeleton has 20 `w3a_` statements** (2 generic +
  6 crossing + 2 `_ne` + 6 `over` + `exists_Ψ₀` + `riii_param` + `exists_Ψ₁` + `exists_params`); the "21" of
  `W3_SKELETON_REPORT.md` §2.2 / the unit prompt is a miscount — its own table lists these 20.
* The moved block (skeleton 345–379: the `/-! ### W3-(a)` header, `G11_centroidSw`, `G11_discOfSw`, `structure
  G11_ParamsSw`) occurs exactly once, byte-identical, in the assembled file (lines 200–235).

## 3. Every remaining `sorry` (10; line = the `  sorry` line)

| line | declaration | unit | status |
|---|---|---|---|
| 4094 | `w3b_reparam_switch` | (b) | optional (no consumer in the file; ≈ 0.15k) |
| 7552 | `w3e_xs_point` | E | Wave 3b |
| 7570 | `w3e_liftVisit_σD_sw` | E | Wave 3b |
| 7603 | `w3e_recordIsoData_sw` | E | Wave 3b |
| 7699 | `w3g_bigonData_smooth_arcST` | G (177 (6)) | Wave 3b |
| 7726 | `w3g_bigonData_smooth_arcTS` | G | Wave 3b |
| 7757 | `w3h_record_core` | H (177 (6)) | Wave 3b |
| 7770 | `w3h_smooth_record_occ` | H | Wave 3b |
| 7779 | `w3h_restrict_switch_deleted` | H | Wave 3b |
| 7820 | `w3h_hrec` | H | Wave 3b |

**Open `w3a_` sub-leaves: none** (BC: `w3a_X₀_generic w3a_X₁_generic w3a_X₀_cross_mp/mq/pq w3a_X₁_cross_pC/qB/pq
w3a_y_ne w3a_y'_ne w3a_over_mp₀/mq₀/pq₀/mp₁/mq₁/pq₁ w3a_exists_Ψ₀ w3a_exists_params`; DE: `w3a_riii_param
w3a_exists_Ψ₁`).  The word `sorry` occurs in no docstring; 10 = the `declaration uses sorry` count.

## 4. `#print axioms` (scratch copy `W3_A1_Axioms.lean` = the file + 49 `#print axioms` lines; exit 0, 48 s)

| declaration | axioms |
|---|---|
| **`SM.Link.G11_core_sw`** (the Wave-3 leaf) | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — **no `sorryAx`** |
| **`SM.Link.esc_switch_riii_of_chain`** (row 177 (4)) | same six — **no `sorryAx`** |
| `SM.Link.w3e_strong_case_sw` | the six + **`sorryAx`** — enters ONLY through `w3e_xs_point`, `w3e_liftVisit_σD_sw`, `w3e_recordIsoData_sw` (each `[propext, sorryAx, Classical.choice, Quot.sound]`); the other W3E declarations `w3e_alt_flip w3e_trans_sw_of_alt w3e_alt_of_completeLocal w3e_swPair w3e_cfg_trans_sw w3e_configOfSw w3e_configOfSw_D₀sw` are sorry-free |
| all 20 `w3a_*`, `w3de_riii_param`, `w3de_exists_Ψ₁`, `w3de_moveMatch_withOver`, `w3c_riii_sw`, `w3d_exists_Ψ₁_sw`, `w3c_htrans_sw`, `w3b_isRecordIsoData_switch`, `w3b_localFrame_switch` | `[propext, Classical.choice, Quot.sound]` |
| `w3c_homfly_M₁sw` | standard + `SM.lit_homfly` (RIII invariance of the literature HOMFLY) |
| `w3b_reparam_switch`, `w3g_*` (2), `w3h_*` (4) | `sorryAx` (their own bodies) |

`SM.lit_homfly` (`SM/LinkInterfaces.lean` :127), `SM.lp_lm` (:181), `SM.lp_lm_uniqueness` (:241) are the registered
literature axioms the Wave-1 report already lists for `esc_switch_riii_of_chain`; they enter through `SM.BigonDeletion`
/ the ledger side, not through the copy.  (Wave 1's row for `G11_core_sw` read `sorryAx` — that was the open leaf itself.)

## 5. Name-clash scan (`clash_scan_W3.py work/lean W3_A1_Assembled.lean`, namespace-aware)

1096 declarations, 1096 distinct fully-qualified names, 0 internal duplicates, **0 fully-qualified clashes** with
any declaration in `work/lean/**/*.lean` (excluding `.lake`).  925 short-name coincidences, all informational and
expected: `SM.Link.G11_ParamsSw.<gu*>` mirrors `RProof.G11_Params.<gu*>` (the copy keeps every `gu3…gu6` name),
`SM.Link.G11_ConfigSw.<comp, v_*, σ, σD, D₀, …>` mirrors `RProof.G11_Config.<…>`, plus a handful of generic
short names (`mid`, `U`, `comp`) in unrelated namespaces (`SM.FrontRealize`, `SM.SpatialLink`, `SM.FrontRows`).
Inside the new file the two `open RProof.G11_Params (…)` lists (BC: 66 `gu3/gu4/gu5` names; DE: 52 `gu6` names) are
disjoint from each other and from every declaration of the other block, so no ambiguous-overload risk was created
by the join (the compile confirms).

## 6. What is left for Wave 3b (honest state and line estimates)

The copy itself is DONE: 905 of the accepted namespace's 908 `π/C`-dependent declarations (BC 512 + DE 393) are
re-derived over `G11_ParamsSw`; the three not copied are by design (`gu6_htrans` → the `htrans` hypothesis of
`w3a_riii_param`; `riii` → its parametrised form `w3de_riii_param`, the positive instance recoverable as in the DE
report §6; `homfly_M₁`/`core_of_params` → the skeleton's `w3c_homfly_M₁sw`/`G11_core_sw`).  Remaining:

| item | what | est. lines | source / template |
|---|---|---|---|
| **Unit E** (3 sub-leaves, the only `sorryAx` in `w3e_strong_case_sw`) | `w3e_xs_point` (three cases on `sw`: `gu3_crossingPoint_symm` + `G11_carrierEdge_crossingPoint` :8976); `w3e_liftVisit_σD_sw` (copy of `G11_liftVisit_σD` :10793 with a `halt`-free `gu6_lift_six` :10758); `w3e_recordIsoData_sw` (copy of `G11_recordIsoData` :10852–10920 with the switched bits at `x, x'` via `w3b_*`) | **0.7–0.9k** (0.15 + 0.25 + 0.3–0.5) | `W3_SKELETON_REPORT.md` §1.3, §2.6 |
| **Unit G** (177 (6) sites) | `w3g_bigonData_smooth_arcST`, `_arcTS` (`j = 2` bigon data on `smoothDiagram` outputs; try deriving TS from ST through `Diagram.reverse`) | **2.0–2.4k** | BigonDeletion §2a, Smoothing §3–§6 |
| **Unit H** (177 (6) record side) | `w3h_restrict_switch_deleted` (0.06k), `w3h_smooth_record_occ` (0.2k), `w3h_record_core` (1.2k, the eight orientation patterns), `w3h_hrec` (0.4k) | **1.9k** | LinkRecord / Smoothing §8 |
| **W3-I, the (4) realiser** | `esc_MoveData.switch_riii` from `w3e_strong_case_sw` with `carrierDiagram = geoPositiveLift` (`unfold CV.carrierDiagram`), the relabelling case split as in `GT_G11_strong_proof` (:10995–11007, 13 lines), `w3e_alt_of_completeLocal` + `w3e_trans_sw_of_alt` for `trans_sw`, the nonzero-sign side condition (D3) | **0.3–0.5k** | `W3_SKELETON_REPORT.md` §6 W3-I, §4 D3 |
| **W3-I, the (6) realiser** | `esc_MoveData.rii_after_smoothing` (weak form `esc_rii_after_smoothing_weak`) from `w3g_*` + `w3h_hrec` + `esc_rii_after_smoothing_of_bigons` (`SM/BigonDeletion.lean` :5313); the orientation caveat D4 and the `same_over` data D5 must be supplied here | **0.4–0.8k** (D4/D5 not yet derived — the riskiest open point) | §4 D4–D6 |
| **F-177-2, the `esc_interface` replay** | add `(hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)` to the hypotheses of `esc_interface` (`RProof/RALedgers.lean` :2027, the only definition; consumers `esc_couple` :2277 and `esc_ledger` :2330 in the same file, no other module mentions it), obtain them in `esc_couple` from `hE, hR` by `generic_table E e f g h3 h4e h4f h4g hE` + `SEL_genericTableData_mono` as `generic_transport` :11157 does; re-check `RALedgers.lean` | **≈ 10–30 lines**, one re-check of the 2371-line module (D-F11-internal edit; the row's statement is unchanged) | §1.4, §4 D2 |
| the port | move `W3_A1_Assembled.lean` out of drafts: `RProof/GenericTransportSw.lean` (or `…SwBC.lean` ≈ 3.7k + `…SwDE.lean` ≈ 2.7k as D1 suggests) + the skeleton material next to `SM/BigonDeletion.lean`; `lake build`; the per-file check is 36 s here, so a single 7.8k-line module is acceptable | 0 new lines | §4 D1 |
| optional | `w3b_reparam_switch` (0.15k); the positive instance `riii : RIII π.M₀ π.M₁` over `G11_ConfigSw` is NOT restatable without a transitivity hypothesis — by design, not a gap | — | DE report §6 |

Total new material for Wave 3b: **≈ 5.3–6.6k lines** (E 0.7–0.9k, G 2.0–2.4k, H 1.9k, realisers 0.7–1.3k, interface
≤ 0.03k), consistent with the skeleton report's "≈ 6k genuinely new"; the ≈ 6.4k mechanical copy it budgeted is now
in hand at 6.4k lines (3711 + 2654) and compiles in 36 s, not minutes.

## 7. Pitfalls / notes for the executor

* Anchor on names, not skeleton line numbers (the skeleton report's numbers are offset by 8; BC's file moved a
  block; the DE block sits after `M₁sw_componentCount`, 2.7k lines before the connectors it serves).
* The join needed no edits because both provers kept the accepted literal `⟨k + 3, π.hk₃, π.X₀⟩` in copied
  statements and let the skeleton's `comp₀`/`w3a_*` names meet them only in the connectors (`exact`, defeq).  Keep that
  rule for unit E: state copied lemmas with the accepted text, connect at the `w3e_` boundary.
* `#print axioms` on a scratch copy is the reliable sorry audit (`grep sorry` misses nothing here, but it would
  miss a `sorry`-carrying import); the two literature axioms `SM.lp_lm*` enter through `SM.BigonDeletion`, as in Wave 1.
* `if_pos`/`if_neg` deprecations (14) are in the skeleton's `x₀_eq*`/`x₁_eq*` and `w3e_swPair` proofs; cosmetic,
  fix with `ite_eq_left`/`ite_eq_right` (or `simp [*]`) at port time if the lane wants clean logs.
