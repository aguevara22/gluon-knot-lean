# W6_ASSEMBLY_REPORT — corner wave 6 (row 110 `thm:C-S7`) MERGE, 2026-09-19 12:55 UTC / 8:55am ET (under D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W6_Assembled.lean`** (27,533 lines, sha256 `425724bc9bed22b1…`) = `W5_Assembled.lean` (25,237 lines,
`69b01559712ba9b7…`) + the FOUR wave-6 unit blocks VERBATIM (CURL `w6k_` 357 lines, COR `w6c_` 436, ROT `w6r_` 531, CC `w6x_` 785;
1,450 new declarations against `Statements_FINAL.lean`, 84 more than W5) + COR's body of `w5r_box_corners` (9 lines) + CC's body of
`w6r_box_centreCorners` (9 lines) + the `w6_` assembly glue (9 declarations, 168 lines, `section W6Glue` 27225-27392) + ONE token changed
in the body of `w4_box_returnedRows` (`w5_box_branch` → `w6_box_branch`) + **the bigon leaf's `sorry` replaced by its recorded closure line**.
`diff W5_Assembled.lean W6_Assembled.lean | grep '^[0-9]'` = `1,8c1,10` (header) + `24298a24301,24657` (CURL) + `25067a25427,25862`
(COR block) + `25073c25868,25876` (`  sorry` of `w5r_box_corners` → COR's proof) + `25096a25900,27392` (ROT block with CC's block and body
inside + glue) + `25106c27402` (the one token) + `25194c27490` (`  sorry` of `s7_bigon_law_at` → the closure line); the deleted side is
W5's eight header lines, the two `  sorry` lines and that one `obtain` line.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W6_Assembled.lean`, 45 s): **0 errors, 0 warnings other than exactly
8 `declaration uses sorry`, ALL DEAD** — 4441 `s7q_box_ret`, 18057 `s7z_F_exists`, 18498 `s7z_returned_of_FSector` (W3/K, superseded),
23883 `w5b_box_returnedData`, 24280 `w5b_box_interlacingTurnData`, 24289 `w5b_box_noninterlacingTurnData`, 24663 `w5b_box_curlData`
(BR, superseded), 25893 `w5r_box_branch` (ROW, superseded).  **`#print axioms thm_C_S7` = `[propext, Classical.choice, Quot.sound,
SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` — the nine registered
axioms, NO `sorryAx`.**  `grep -c sorry` = 21 = 8 bodies + 13 prose mentions.  `tools/stmt_check.py --base W3_Skeleton.lean` 5/5 PASS;
`tail -n 43` identical to `W3_Skeleton.lean`; `tools/clash_scan.py`: `duplicates_in_assembled: []`, `full_name_clashes: {}` (46 short-name
coincidences in other namespaces).  No `#print`/`#check`/`#eval`.  Nothing written under `work/lean`; `lake build` never run.
**Port prepared: `work/drafts/corner/port/CS7/`** (§7; `SM/CS7Units.lean`, `SM/CS7.lean`, `SM/ComparisonRows.lean`, `PORT_REPORT.md`, `tools/`).

## 0. In one paragraph

**Row 110 `thm_C_S7` is sorry-free on the nine registered axioms; the bigon leaf is closed; rows 127/128 are one-liners in the port.**
W6-COR closed ROW's `w5r_box_corners` (standard axioms).  W6-ROT proved both rotation identities of BR's turn boxes per `(t, T₀)` from the
corner data and a NEW consumed Prop, the centre corner data `w6r_CentreCornerData` (principal-turn form of the correspondence on A2's
centre polygon `L*`), stated as the radius-form box `w6r_box_centreCorners`; **W6-CC** (a unit spawned on ROT's report, `W6_CC.lean`,
`W6_CC_REPORT.md`) closed that box (standard axioms) — its block sits inside ROT's `section W6Rot` before the box, as ROT's file has it.
W6-CURL proved the curl box in the corrected form `w6k_box_curlData` (six radius facts added; the box as stated is not derivable,
W6_CURL_REPORT §2).  BR's three boxes are per-`t` statements without a radius / without the radius facts, so none of the deliverables
can replace their bodies; the glue (§3) rebuilds the branch data from the deliverables (`w6_interlacingTurnData`,
`w6_noninterlacingTurnData` = rotation from ROT + patterns from U110-C on the corner data; `w6_interlacingData`, `w6_noninterlacingData`
= BR's wrappers with the box calls swapped; `w6_branchData`, `w6_box_branch` = W5's glue with the corner and centre data threaded, radii
of `w5r_box_corners` and `w6r_box_centreCorners` intersected), `w4_box_returnedRows` calls `w6_box_branch`, and — its input now
sorry-free — the leaf closes as `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`.  The complete axiom census
(every top-level name) shows `sorryAx` on exactly 19 dead declarations (§5), all dropped in the port.  A second assembler instance (B)
worked in parallel on the same wave and writes `W6_Assembled_B.lean`, `W6_ASSEMBLY_REPORT_B.md`, `port/CS7_B/` (§8.6).

## 1. Task (1): unit diffs against `W5_Assembled.lean` — all clean

| unit | prefix | hunks | block lines (decls) | sorried bodies added | body replaced |
|---|---|---|---|---|---|
| COR | `w6c_` | vs W5: `25067a25068,25503` + `25073c25509,25517` (deleted side `  sorry`) | 436 (10) | none | `w5r_box_corners` (→ 9 lines) |
| ROT | `w6r_` | vs W5: `25096a25097,25627` | 531 (20) | 1: `w6r_box_centreCorners` (consumed Prop) | none |
| CURL | `w6k_` | vs W5: `24298a24299,24655` | 357 (23) | none | none (`w5b_box_curlData` kept as stated) |
| CC | `w6x_` | vs W6_ROT: COR's two hunks + `25590a26035,26819` + `25597c26826,26834` (deleted side `  sorry`) | 785 (33) | none | `w6r_box_centreCorners` (→ 9 lines) |

Each unit file = its base + one insertion (+ one body): COR inside `section W5Row` before the docstring of `w5r_box_corners`; ROT inside
`section W4Bigon` after `end W5Row`; CURL inside `section W5BRData` before `w5b_box_curlData`; CC inside ROT's `section W6Rot`
immediately before the docstring of `w6r_box_centreCorners` (CC's base `W6_CC.lean` = W5 + COR's two hunks + ROT's block, verified
line-by-line by `assemble.py`).  `stmt_check` 5/5 PASS and `tail -n 43` identical for all four; every top-level name carries the unit
prefix; no unit added an import, `open`, `attribute` or top-level `variable`; no statement, name or docstring of the base touched (CC
included: ROT's docstring of the box is intact).  Clash scans (unit reports): duplicates `[]`, clashes `{}`.

## 2. Task (2): layout of `W6_Assembled.lean`

| W6 lines | content |
|---|---|
| 1-10 | assembly header (`--` comments) |
| 11-24300 | W5 lines 9-24298 verbatim (through the structure `w5b_CurlData`) |
| 24301-24657 | **CURL** block verbatim (`section W6CurlRecord`: `w6k_gap_curl`, `w6k_gap_rest`, `w6k_P_eq_one_of_two_occ`, `w6k_P_eq_of_curl`; `section W6Curl` 24480: `w6k_X`, `w6k_curl_adjacent`, **`w6k_box_curlData` 24573**) |
| 24658-25426 | W5 24299-25067 verbatim (`w5b_box_curlData` 24663 sorried UNUSED; BR's wrappers UNUSED; `section W5Row`; W5 glue `section W5Glue`: `w5_returnedData`, `w5_transportData`, `w5_contactData`, `w5_branchData` 25294 UNUSED, `w5_returnedRow_of`, `w5_box_branch` 25402 UNUSED; `w5r_box_transport` proved) |
| 25427-25862 | **COR** block verbatim (`section W6Cor`: `w6c_glued_corners` abstract, `w6c_turn_M_of_gt`, `w6c_chi_P₂`, `w6c_turn_firstHalf_zero`, `w6c_turn_secondHalf_zero`, `w6c_interlacing_iff`, `w6c_turn_M`, **`w6c_glued_corners_wall`**, **`w6c_cornerData` 25836**) |
| 25863-25867 | W5 25068-25072 verbatim (docstring + statement of `w5r_box_corners` 25866) |
| **25868-25876** | **COR's body of `w5r_box_corners`** |
| 25877-25899 | W5 25074-25096 verbatim (`w5r_box_contact` proved, `w5r_box_branch` 25893 sorried UNUSED, `end W5Row`) |
| 25900-27222 | **ROT** block verbatim with **CC** inside (`section W6Rot` 25900: `w6r_sign_eq_of_ne_zero`, `w6r_principalTurn_of_splice`, `w6r_Lstar`, `w6r_turn_Lstar`, `w6r_CentreCornerData`, `w6r_weight_qH`, `w6r_rotationInt_qL`, `w6r_patterns_*`, `w6r_centreCornerData_of_splice`, **`w6r_rotation_interlacing` 26298**, **`w6r_rotation_noninterlacing` 26333**, `end W6RotAt`; **CC block `section W6CC` 26394-27177**: `w6x_Chain`, `w6x_gap_not_corner`, `w6x_chain_inl/inr`, **`w6x_glued_order` 26795**, `w6x_cramer_of_line`, `w6x_point_mark_first/second`, `w6x_hcol`, `w6x_hμ`, **`w6x_centreCornerData` 27135**; ROT's docstring + statement of **`w6r_box_centreCorners` 27183** with **CC's body 27189-27197**; `w6r_exists_rotation` 27198 (now sorry-free, unused by the glue); `end W6Rot` 27222) |
| **27224-27392** | **`w6_` glue `section W6Glue`** (§3) |
| 27393-27396 | W5 25097-25100 verbatim (docstring + statement of `w4_box_returnedRows` 27396) |
| 27397-27417 | W5's 21-line body with `w5_box_branch` → **`w6_box_branch`** at 27402 |
| 27418-27533 | W5 25122-25237 verbatim except **line 27490** (the leaf's `  sorry` → `  exact w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`): `w4_s7_bigon_law_at_of`, `end W4Bigon` 27471, the leaf `s7_bigon_law_at` 27481, `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7` 27529 — the last 43 lines byte-identical to `W3_Skeleton.lean` |

Order constraints honoured: COR before ROT (ROT's `w6r_exists_rotation` calls `w5r_box_corners`, so ROT must follow that box, i.e. `end
W5Row`); CC inside ROT before the box it closes (as in `W6_CC.lean`); CURL before `w5b_box_curlData` and before the glue; the glue after
ROT/CC (it calls `w6r_*`, and `w6_box_branch` calls `w6r_box_centreCorners`) and after CURL.  **Renames: none.  De-duplication: none applied.**

### Black boxes connected / not connected

| box (unit) | producer | connected |
|---|---|---|
| `w5r_box_corners` (ROW) | COR's `w6c_cornerData` (body by COR) | **YES** — `[propext, Classical.choice, Quot.sound]` |
| `w6r_box_centreCorners` (ROT's consumed Prop) | CC's `w6x_centreCornerData` (body by CC) | **YES** — standard axioms |
| `w5b_box_interlacingTurnData` (BR, 24280) | ROT's `w6r_rotation_interlacing` + `w6r_patterns_interlacing` via **`w6_interlacingTurnData`** | **In substance YES, in shape NO**: the box is per-`t` without a radius and ROT's theorem needs `hCC hL`, which hold only below the radii of `w5r_box_corners` / `w6r_box_centreCorners` for eligible `T₀`.  Box sorried and UNUSED; its Prop delivered under `hCC hL` by the glue |
| `w5b_box_noninterlacingTurnData` (BR, 24289) | `w6r_rotation_noninterlacing` + `w6r_patterns_noninterlacing` via **`w6_noninterlacingTurnData`** | likewise |
| `w5b_box_curlData` (BR, 24663) | CURL's **`w6k_box_curlData`** (six radius facts added) | **In substance YES, in shape NO** (W6_CURL_REPORT §2); box sorried and UNUSED; `w6_noninterlacingData` calls `w6k_box_curlData` |
| `w4_box_returnedRows` (W4 glue, B2') | `w5_returnedRow_of` on the radii of `s7f_exists_bigonSplit`, `s7a2_exists_intervalLocal`, `w5r_box_transport`, `w5r_box_corners`, `w5r_box_contact`, **`w6_box_branch`** | **YES** — `[propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]`, no `sorryAx` |
| `s7_bigon_law_at` (leaf) | `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` | **WIRED** (line 27490); frozen statement byte-identical; axioms as `w4_box_returnedRows` |

## 3. Task (2), the glue (`section W6Glue`, 27225-27392; variables `hn g {M a} h h₁ h₂` of `W4Bigon`; `section W6GlueAt` adds
`t T₀ {r η δ} hloc ht hr hr0 hr1 hη hηr hηr1 hCC hL`, `section W6GlueTurn` adds `hT₀ hS₁ hS₂`; included per theorem)

1. `w6_signType_neg_ne_zero (s) (hs : s ≠ 0) : -s ≠ 0`, `w6_signType_neg_neg (s) : -(-s) = s` (`cases s <;> …`).
2. **`w6_interlacingTurnData hn g h h₁ h₂ t T₀ hloc ht hCC hL hT₀ hS₁ hS₂ hI hW : w5b_InterlacingTurnData …`** (27275): `hW' := w6r_weight_qH …
   hW` (`wt(q_H) ≠ 0`); `⟨-, hall₁, hall₂⟩ := w6r_patterns_interlacing … hI hW' hCC`; `⟨w6r_rotation_interlacing … hI hW hCC hL,
   s7c_signedUniformOrOneDissent_of_forall _ (w5r_sgn_ne_zero g h t) hall₁, … hall₂⟩` (ROW's and BR's spellings of `L₁`, `T₁` unify by `exact`).
3. **`w6_noninterlacingTurnData … hI hW : w5b_NoninterlacingTurnData …`** (27288): `⟨j₁, j₂, -, hj₁, hrest₁, hj₂, hrest₂⟩ :=
   w6r_patterns_noninterlacing …`; patterns by `s7c_signedUniformOrOneDissent_of_dissent _ hs jᵢ (by rw [w6_signType_neg_neg]; exact hjᵢ) hrestᵢ`
   with `hs : -s₀ ≠ 0`.
4. **`w6_interlacingData … hloc ht hr hr0 hr1 hη hηr hηr1 hCC hL hT₀ hS₁ hS₂ hT hRT hI hW DA ι`** (27302), **`w6_noninterlacingData`** (27322):
   BR's wrapper statements verbatim (`hT hRT` explicit), bodies with the box calls swapped for `w6_interlacingTurnData` /
   `w6_noninterlacingTurnData` and `w6k_box_curlData … hS₁ hr0 hr1 hr hη hηr hηr1 DA i hc₁` (CURL's §3 swap, in the copy rather than in BR's block).
5. **`w6_branchData … hloc ht hr hr0 hr1 hη hηr hηr1 hCC hL hmem hT hW : w5r_BranchData …`** (27345): W5's `w5_branchData` with the wrapper calls swapped.
6. **`w6_box_branch hn g h h₁ h₂`** (27379; `w5_box_branch`'s statement): radius `min δ₁ (min δ₂ δ₃)` of `s7a2_exists_intervalLocal`,
   `w5r_box_corners`, `w6r_box_centreCorners`; body `w6_branchData`.
7. **Body of `w4_box_returnedRows`** (27397-27417): W5's body, one token (27402).  **Body of the leaf** (27490): the recorded closure line.

The glue compiled in place on the FIRST attempt at 12:11Z (against COR+ROT+CURL, with `w6r_box_centreCorners` still sorried; the
wiring was shape-checked on a scratch copy at 12:23Z); CC's block and body were merged mechanically at 12:40Z (`assemble.py`,
assert-guarded), the leaf wired, full compile 0 errors.  Prefix olean for probes: `<scratchpad>/w6asmA/pfx/W6AsmPrefix.olean`.

## 4. Task (3): compile, axioms, frozen statements, clash scan

Compile: §header.  `#print axioms` on EVERY top-level name of the file (1,455 names, 1,400 printable; scratch `<scratchpad>/w6asmA/W6_AllAxioms.lean`,
`allax.log`; standard = `propext`, `Classical.choice`, `Quot.sound`; registered literature axioms `lit_homfly`, `lit_homfly_descent`, `lp_lm`,
`lp_lm_uniqueness`, `ng_finite_word`, `src_contact`; **no unregistered axiom anywhere**):

| declaration | sorryAx | other axioms |
|---|---|---|
| **`thm_C_S7`** | **NO** | **standard + all six literature (the nine registered)** |
| `thm_C_S7_of_floor`, `thm_C_S7_of`, `s7_bigon_law_at`, `s7_sliding_law_at`, `w4_s7_bigon_law_at_of`, **`w4_box_returnedRows`**, **`w6_box_branch`**, **`w6_branchData`**, **`w6_noninterlacingData`**, **`w6k_box_curlData`**, `w5_returnedRow_of`, `w5r_box_transport` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` |
| `w6k_P_eq_of_curl` | no | standard + `lp_lm` |
| **`w6r_box_centreCorners`**, `w6x_centreCornerData`, `w6x_glued_order`, `w6r_exists_rotation`, **`w6_interlacingData`**, **`w6_interlacingTurnData`**, **`w6_noninterlacingTurnData`**, `w6r_rotation_interlacing`, `w6r_rotation_noninterlacing`, `w6r_patterns_*`, `w6r_principalTurn_of_splice`, **`w5r_box_corners`**, `w6c_cornerData`, `w6c_glued_corners_wall`, `w6k_curl_adjacent`, `w5r_box_contact` | no | standard only |
| the 19 dead declarations of §5 | YES | — |

Frozen statements: `python3 tools/stmt_check.py W6_Assembled.lean --base W3_Skeleton.lean` → 5/5 byte-identical and unique (PASS);
`tail -n 43` identical to `W3_Skeleton.lean`.  Clash scan: §header.  Verbatim check: `<scratchpad>/w6asmA/assemble.py` is assert-guarded
(every unit block located by its diff anchors, every other line of every unit file asserted equal to its base, CC's file asserted equal to
W5 + COR + ROT outside its two hunks).

## 5. State: sorry-free; the `sorryAx` census

Exactly **19 declarations carry `sorryAx`**, all DEAD (on no proved path; the census is closed under "used only by dead material" since
every consumer of a sorried box is itself sorried): W3's `s7q_box_ret`, `s7q_box_rows`, `s7q_exists_contactSector`,
`s7q_sliding_law_at_of_boxes`, `w3_SlidingRet_of_box`, `s7z_F_exists`, `s7z_returned_of_FSector`, `s7z_exists_rowSector`,
`w3_BigonFSector_of_box`, `w3_BigonReturnedRows_of_box`; W5's `w5b_box_returnedData`, `w5b_box_interlacingTurnData`,
`w5b_box_noninterlacingTurnData`, `w5b_box_curlData`, `w5b_interlacingData`, `w5b_noninterlacingData` (BR), `w5r_box_branch` (ROW),
`w5_branchData`, `w5_box_branch` (W5 glue).  All are dropped in the port (§7); the pruned file compiles with 0 errors and 0 warnings.
Remaining Props: **none.**

## 6. Wave 7: none needed for row 110

The corner chain's row 110 is complete; rows 127/128 follow by their `_of` theorems (port).  Next for the executor: copy the port modules
(§7), fill the header time, `lake build`, update `lean-declarations.json` (`thm:C-S7`, `thm:comparison`, `cor:C-inherits` → their fixed
names).

## 7. Task (4): port — READY: `work/drafts/corner/port/CS7/` (details in its `PORT_REPORT.md`)

| module | lines | compile (module semantics, scratch object tree) | axioms |
|---|---|---|---|
| `SM/CS7Units.lean` | 27,164 | 0 errors, 0 warnings; 63 s (not split) | — |
| `SM/CS7.lean` | 93 | 0 errors, 0 warnings; 19 s; `stmt_check --base W3_Skeleton.lean` 5/5 PASS | `thm_C_S7`: the nine registered, no `sorryAx` |
| `SM/ComparisonRows.lean` | 22 | 0 errors, 0 warnings; 24 s | `thm_comparison`, `cor_C_inherits`: the nine registered, no `sorryAx` |

Pipeline (scripts in `port/CS7/tools/`): `prune.py` deletes the 19 dead declarations with their docstrings/`include` lines (291 lines);
`port_build_w6.py` writes the three modules (units verbatim minus the leaves and the row tail; 23 exact-text rewordings: the 7 surviving
prose `sorry` mentions and the "BLACK BOX … NOT proved" docstrings of 13 proved theorems — PORT_REPORT §3; it refuses any `sorry`/`#print`/
`#eval`/`#check`/`admit` string); `compile_port.sh` compiles in a scratch object tree in import order and prints the axioms.  Header line 1 of
each module: `-- Ported <HH:MM>Z 2026-09-19 from work/drafts/corner/W6_Assembled.lean by the pod executor (files prepared by the W6-GLUE
assembler)`.  Collapses (W5 §7): none applied — the duplicated spellings are threaded through hundreds of call sites (PORT_REPORT §4 lists them).
Four `set_option linter.unusedSectionVars false in` lines (W4 §8.2) remain in the units module — disclosed.

## 8. Deviations and assembler's edits, disclosed

1. **The bodies of `w5b_box_interlacingTurnData` / `w5b_box_noninterlacingTurnData` were NOT written** although the task says to write
   them: as stated (per `t`, `hloc ht` for arbitrary `r η δ`, no radius, `hT₀ hS₁ hS₂` instead of `T₀ ∈ w4_EligDec`) they are not derivable
   from ROT's deliverables, which need the corner data and the centre data — Props that hold only below radii and for eligible
   decompositions.  Whether the boxes are TRUE as stated is untested.  Following W5 §8.4 (the treatment of `w5r_box_branch` /
   `w5b_box_returnedData`), the boxes stay sorried and UNUSED and their Props are delivered under `hCC hL` by the glue.  Likewise
   `w5b_box_curlData` (CURL's disclosure): CURL's one-token swap is applied in the glue's COPY of BR's wrapper, not in BR's verbatim block.
2. **W5's glue `w5_branchData` / `w5_box_branch` is left in place, verbatim, dead** (it precedes ROT's block, which must follow
   `w5r_box_corners`, so it cannot call `w6r_*`); the replacements sit after ROT/CC and `w4_box_returnedRows`' body switches one token.
3. **CC's block is inside ROT's block** (between `end W6RotAt` and the docstring of `w6r_box_centreCorners`), exactly as `W6_CC.lean` has
   it; so "ROT's block verbatim" holds up to that one insertion and the one body — the S1P/W5 precedent.  CC was not among the three
   units named in the task; it was spawned on ROT's report and finished at 12:36Z; the executor confirmed it final.
4. **Docstrings of my own glue edited** at the CC merge (three sentences: `w6_branchData`, `w6_box_branch`, the `W6Glue` intro no longer
   speak of `sorryAx`); no unit text touched.  Header: W5's eight comment lines replaced by ten (`1,8c1,10`).
5. The reassessment rule was not triggered (the glue compiled on the first attempt; CC's merge needed one off-by-one fix in the assembly
   script's guard, no Lean change).
6. **A second W6-GLUE assembler instance (B) ran in parallel** (spawned ~12:04Z) and, before noticing this one, overwrote the scratch files
   `glue.lean`, `assemble.py`, `header.lean`, `hdr.lean`, `ftr.lean`, `lean.sh`, `build_pfx.sh` in `<scratchpad>/w6asm/` at 12:11:50-12:13:01Z
   (its note `NOTE_FROM_SECOND_ASSEMBLER.md` there) — two seconds AFTER this instance's first `W6_Assembled.lean` was written, so that file
   and its compile (12:11-12:12Z) are this instance's own glue; this instance moved to `<scratchpad>/w6asmA/`, recovered its glue verbatim
   from its own `W6_Assembled.lean`, and everything after 12:38Z was done there.  B writes `W6_Assembled_B.lean`, `W6_ASSEMBLY_REPORT_B.md`,
   `port/CS7_B/` (the W5 precedent); this instance owns `W6_Assembled.lean`, this report and `port/CS7/`.  The two assemblies are independent
   (same unit blocks, different glue).

## 9. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W6_Assembled.lean        # 0 errors; 8 × "declaration uses sorry" (4441 18057 18498 23883 24280 24289 24663 25893), all dead; 45 s
cd work/lean && lake env lean <scratchpad>/w6asmA/W6_AllAxioms.lean       # #print axioms on all 1,455 names: thm_C_S7 = the nine registered; sorryAx on exactly the 19 dead; log allax.log
python3 work/drafts/corner/tools/stmt_check.py work/drafts/corner/W6_Assembled.lean --base work/drafts/corner/W3_Skeleton.lean   # 5/5 PASS
python3 work/drafts/corner/tools/clash_scan.py work/drafts/corner/W6_Assembled.lean   # duplicates [] / full_name_clashes {} / 1450 new decls
tail -n 43 work/drafts/corner/W6_Assembled.lean | diff - <(tail -n 43 work/drafts/corner/W3_Skeleton.lean)   # identical
diff work/drafts/corner/W5_Assembled.lean work/drafts/corner/W6_Assembled.lean | grep '^[0-9]'   # 1,8c1,10 24298a24301,24657 25067a25427,25862 25073c25868,25876 25096a25900,27392 25106c27402 25194c27490
for u in COR ROT CURL; do diff W5_Assembled.lean W6_$u.lean | grep '^[0-9<]'; done; diff W6_ROT.lean W6_CC.lean | grep '^[0-9]'   # §1
grep -c sorry work/drafts/corner/W6_Assembled.lean   # 21 (8 bodies + 13 prose) ; grep -n "#print\|#check\|#eval" → none
python3 port/CS7/tools/prune.py W6_Assembled.lean W6_Pruned.lean <19 names> ; python3 port/CS7/tools/port_build_w6.py W6_Pruned.lean <out> ; port/CS7/tools/compile_port.sh <out>   # §7
```
Reproduce the merge: `<scratchpad>/w6asmA/assemble.py` (inputs `header.lean`, `glue.lean`, `body_rows.lean`; writes the file and the
prefix).  Timeline (UTC): 12:04 start; 12:05 unit diffs; 12:10 glue; 12:11 assembled, full compile 0 errors (55 s); 12:13 axioms; 12:20
first report (state: one open box, wave-7 spec); 12:23 wired-leaf shape check; 12:24 axiom census; 12:26 pruning validated; 12:30 port
pipeline validated modulo the box; 12:36 CC's report; 12:38 second-assembler collision noticed, moved scratch; 12:40 CC merged + leaf wired,
full compile 0 errors (46 s); 12:42 census (19 dead), checks; 12:44-12:48 port built, compiled, installed; 12:55 reports.
