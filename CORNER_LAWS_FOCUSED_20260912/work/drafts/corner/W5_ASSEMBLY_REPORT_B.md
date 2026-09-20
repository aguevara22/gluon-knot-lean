# W5_ASSEMBLY_REPORT_B — corner wave 5 (row 110 `thm:C-S7`) MERGE, assembly B, 2026-09-19 11:25 UTC / 7:25am ET (under D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W5_Assembled_B.lean`** (25,160 lines, sha256
`7f79c022c8111e48edffd4a851080f409541bc994f1147a30434fa3c111b5ca9`) = `W4_Assembled.lean` (19,974 lines, `9c0ec3b7…`) + the
four wave-5 unit blocks in dependency order (RT `w5t_` 2,599 lines verbatim, SITE `w5s_` 245 verbatim, BR `w5b_` 1,656 verbatim,
ROW `w5r_` 477 with the two disclosed edits of §2.3) + the `w5_` glue (5 declarations, 137 lines, inside ROW's `section W5Row`
before its boxes) + four body replacements (ROW's boxes `w5r_box_transport`, `w5r_box_contact`, `w5r_box_branch`; the W4 glue box
`w4_box_returnedRows` with ROW's 21-line composition).  `diff W4_Assembled.lean W5_Assembled_B.lean` = `1,6c1,8` (header) +
`19853a19856,25018` (ONE insertion) + `19858c25023,25043` (`  sorry` → ROW's body); the deleted side is the six W4 header lines and
that one `  sorry`.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W5_Assembled_B.lean`, 52 s): **0 errors, 0 warnings other than exactly
9 `declaration uses sorry`** — 4439 `s7q_box_ret`, 18055 `s7z_F_exists`, 18496 `s7z_returned_of_FSector` (W3/K, superseded),
23881 `w5b_box_returnedData` (BR, superseded by the glue's `w5_returnedData`, UNUSED), **24278 `w5b_box_interlacingTurnData`,
24287 `w5b_box_noninterlacingTurnData`, 24304 `w5b_box_curlData` (BR's three OPEN boxes), 24988 `w5r_box_corners` (ROW's OPEN box, no
producer in wave 5)**, 25107 `s7_bigon_law_at` (the leaf, skeleton `sorry`).  `grep -c sorry` = 21 (9 bodies + 12 prose mentions).
`tools/stmt_check.py W5_Assembled_B.lean --base W3_Skeleton.lean`: 5/5 PASS; `tail -n 43` identical to `W3_Skeleton.lean`;
`tools/clash_scan.py`: `duplicates_in_assembled: []`, `full_name_clashes: {}` (1,365 new declarations; 45 short-name coincidences,
all in different namespaces).

**PARALLEL ASSEMBLY, disclosed.**  While this assembly was being probed, a second assembler instance (scratch `w5asm/`, started
≈11:00Z) wrote `work/drafts/corner/W5_Assembled.lean` (11:11:56Z, sha256 `69b01559…`, 25,237 lines) and `W5_ASSEMBLY_REPORT.md`
(11:20:11Z).  To avoid clobbering a finished deliverable, this assembly is filed as **`W5_Assembled_B.lean`** with this report.  Both
assemblies merge the same four unit files, prove the same things and leave the same four Props open (§4); they differ only in how
BR's live-selector hypothesis reaches ROW's row (§6, with the independent verification of the canonical file).  Whichever file wave 6
starts from, the open Props are identical.

## 0. In one paragraph

**`thm_C_S7` is NOT sorry-free; the bigon leaf is NOT closed.**  Units RT and SITE are complete and consumed: ROW's `w5r_box_transport`
(RT's `specEquiv`, weights, cut-form coefficients) and `w5r_box_contact` (SITE's `s7k_ContactRowData` at `q_H := w5r_qH`) are PROVED on
the registered axioms.  Unit BR delivered the RECORD fields of BLOCK's branch data (`record`, `ne`, `comp₁`, `comp₂`) but left the TURN
and CURL fields as three explicit black boxes and did not write its report; ROW's `w5r_box_branch` is now wired to BR's deliverables
(`w5_branchData`) and carries `sorryAx` exactly through those three boxes.  ROW's fourth box `w5r_box_corners` (the contact-corner
correspondence with the printed turns; C's `s7c_carrierWeight_interlacing` input) had no producer in wave 5 and keeps its `sorry`.
Hence `w4_box_returnedRows` (Prop B2') has ROW's body and depends on `sorryAx` through EXACTLY FOUR Props: `w5r_box_corners`,
`w5b_box_interlacingTurnData`, `w5b_box_noninterlacingTurnData`, `w5b_box_curlData` (§4).  The leaf keeps the skeleton's `sorry`
(merge rule: its input is not sorry-free); its closure line is unchanged: `w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing
(w4_box_returnedRows hn g h h₁ h₂ hF)`.  `#print axioms thm_C_S7` = `[propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly,
SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` — the nine registered axioms plus `sorryAx`.
Not port-ready (§5).

## 1. Task (1): unit diffs against `W4_Assembled.lean` — all clean

`diff W4_Assembled.lean W5_<U>.lean` (verified 10:45Z; the unit files' first 19,853 lines are byte-identical to W4 and their tails to
W4's tail):

| unit | prefix | hunks | block (unit lines) | decls | sorried bodies in block | compile (my run) |
|---|---|---|---|---|---|---|
| RT | `w5t_` | `19853a19854,22452` | 19854-22452 (2,599) | 146 | 0 | per W5_RT_REPORT: 0 errors, 5 sorry notes (W4's) |
| SITE | `w5s_` | `19853a19854,20098` | 19854-20098 (245) | 20 | 0 | per W5_SITE_REPORT: 0 errors, 5 sorry notes |
| BR | `w5b_` | `19853a19854,21509` | 19854-21509 (1,656) | 136 | 4: `w5b_box_returnedData` 21035, `w5b_box_interlacingTurnData` 21432, `w5b_box_noninterlacingTurnData` 21441, `w5b_box_curlData` 21458 | **verified here** (no unit report exists): 0 errors, 37 s, 9 sorry notes (W4's 5 + the 4 boxes) |
| ROW | `w5r_` | `19853a19854,20330` + `19858c20335,20355` | 19854-20330 (477) | 29 | 4: `w5r_box_transport` 20301, `w5r_box_corners` 20309, `w5r_box_contact` 20316, `w5r_box_branch` 20324 | per W5_ROW_REPORT: 0 errors, 8 sorry notes |

Every unit is a pure insertion immediately before the docstring of `w4_box_returnedRows` (inside `section W4Bigon`, after
`end W4BigonAt`); ROW additionally replaced the single line `  sorry` of `w4_box_returnedRows` (the only deleted line in any unit
diff).  No unit added an import, `open`, `attribute`, `set_option` or top-level `variable`; the five frozen declarations are
byte-identical in all four (`stmt_check` 5/5 in each unit report; re-run here on the assembled files).  **Unit BR is a PARTIAL
unit** (its header docstring says so: record fields proved "modulo ONE black box consumed from unit W5-RT", turn/curl fields "left as
black boxes in this pass", report "W5_BR_REPORT.md" — never written); the assembler compiled `W5_BR.lean` itself (0 errors) before
merging.

## 2. Task (2): layout of `W5_Assembled_B.lean` (dependency order RT, SITE, BR, ROW; glue inside ROW's section before its boxes)

| B lines | content |
|---|---|
| 1-8 | assembly header (`--` comments) |
| 9-19855 | W4 lines 7-19853 verbatim (imports … `end W4BigonAt`, `def w4_BigonReturnedRows`) |
| 19856-22454 | **RT** block verbatim (`w5t_transport` 22116, `w5t_returned_terms` 22400) |
| 22455-22699 | **SITE** block verbatim (`w5s_ContactRowData_e` 22659, `w5s_exists_wall` 22675) |
| 22700-24355 | **BR** block verbatim (`structure w5b_ReturnedData` 23866, `w5b_box_returnedData` 23881 (sorried, unused), turn/curl boxes 24278/24287/24304 (sorried, OPEN), `w5b_interlacingData` 24321, `w5b_noninterlacingData` 24338) |
| 24356-25017 | **ROW** block `section W5Row` with the §2.3 edits: `def w5r_BranchData` 24621 (+ live-selector binder), `w5r_prod_eq_zero_of_sgn_mul` 24690 (new helper, end of `W5RowAlgebra`), `w5r_returnedRow_of` 24712 (+ the `wt(q_L) = 0` case), **glue `section W5Glue` 24831-24967** (§2.2), then the boxes `w5r_box_transport` 24973 (PROVED), `w5r_box_corners` 24988 (**sorry**, open), `w5r_box_contact` 24996 (PROVED), `w5r_box_branch` 25009 (PROVED modulo BR's boxes) |
| 25018-25043 | W4 19854-19857 verbatim (docstring + statement of `w4_box_returnedRows`), then ROW's 21-line body (W5_ROW 20335-20355 verbatim) |
| 25044-25160 | W4 19859-19974 verbatim: `w4_oneNewborn_rows`, `w4_s7_bigon_law_at_of`, `end W4Bigon` 25097, the leaf `s7_bigon_law_at` 25107 (body `sorry`), `end VertexEdge`, `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7` 25155, `end`, `end SM` (last 43 lines = `W3_Skeleton.lean`) |

### 2.1 Black boxes connected / not connected

| box | producer | state |
|---|---|---|
| `w5r_box_transport` (ROW ← W5-RT) | RT's `w5t_transport`, `w5t_x_mem_qH`, `w5t_y_mem_qH`, `specEquiv`, `carrierWeight_first/second`, `coef_first/second`, `w5t_cutFirst_of/_cutSecond_of`, `w5t_carrierRotation_first/second` | **PROVED** (`w5_transportData`; axioms standard + `lit_homfly, lp_lm, lp_lm_uniqueness`) |
| `w5r_box_contact` (ROW ← W5-SITE) | SITE's `w5s_ContactRowData_e`, `w5s_exists_wall` | **PROVED** (`w5_contactData`; standard axioms) |
| `w5r_box_branch` (ROW ← W5-BR) | BR's `w5b_interlacingData`, `w5b_noninterlacingData` (+ RT via `w5_returnedData`, the library smoothing `s7g_cornerHomfly_skein`) | **wired** (`w5_branchData`); `sorryAx` through BR's three turn/curl boxes only |
| `w5r_box_corners` (ROW ← "W5-RT or W5-BR") | none — RT states no corner correspondence for `q_H` (W5_RT_REPORT §4: "not stated here"), BR's turn boxes are downstream of it | **OPEN**, `sorry` kept |
| `w5b_box_returnedData` (BR ← W5-RT) | RT, through the glue's `w5_returnedData` — but NOT in BR's stated shape: BR's box takes only `hloc : s7a2_IntervalLocal hn g M a r η δ` and `ht`, without A2's `hr hr0 hr1 hη` for that `r η`, which RT's `w5t_transport` needs and which `VertexLocalData` does not carry | **superseded**: BR's data theorems take `hRT : w5b_ReturnedData` as a hypothesis, so the glue passes `w5_returnedData` directly; the box stays sorried and UNUSED (drop at port) |
| `w4_box_returnedRows` (W4 ← ROW) | ROW's body (radius intersection of F's split, A2, the four boxes) | body in place; `sorryAx` through `w5r_box_corners` and `w5r_box_branch` (→ BR's boxes) |
| `s7_bigon_law_at` (leaf) | `w4_s7_bigon_law_at_of … (w4_box_returnedRows …)` | keeps `sorry` (merge rule; input not sorry-free) |

### 2.2 The glue (`section W5Glue`, B 24831-24967; `variable (t) {r η δ δ'} (hloc) (hδ) (hr) (hr0) (hr1) (hη) (hηr) (hηr1) (hdet) (ht) (ht') (T₀)` as RT's `W5TWall`)

* `w5_elim_of_symm {α β γ δ} (e : α ≃ β ⊕ γ) F F₁ F₂ (h₁ : ∀ b, F (e.symm (inl b)) = F₁ b) (h₂ …) (x) : F x = Sum.elim F₁ F₂ (e x)` —
  pure `Equiv` bookkeeping (axioms `[Quot.sound]`), needed because `rw [Equiv.symm_apply_apply]` fails on goals mixing ROW's
  `w5r_qH`/`w5r_L₁` with RT's `w5t_qH`/`w5t_L₁` (definitionally equal `owner …` terms, but not at `rw`'s instance transparency).
* `w5_returnedData hloc hr hr0 hr1 hη ht T₀ (hE : s7f_Eligible …) : w5b_ReturnedData hn g h h₁ h₂ t T₀` — `x_mem`/`y_mem` from
  `w5t_x_mem_qH`/`w5t_y_mem_qH`; `first_mem`/`second_mem` from `hRT.firstCrossingQ_mem_carrierCrossings_iff c _ _
  (hRT.owner_inl_eq_qH_iff hη hw)` (resp. `second`/`inr`).  Standard axioms.
* `w5_transportData hloc hδ hr hr0 hr1 hη hηr hηr1 hdet ht ht' T₀ hsplit (hmem : T₀ ∈ w4_EligDec) hT : w5r_TransportData … hT` —
  `e := (hRT.specEquiv hη hw).symm`; weights `hRT.carrierWeight_first/second h.1.2.1 hr hr0/hr1 hη hw hchi hT hd₁/hd₂ L hL`
  (`hd₁ hd₂` from `w4_eligibleEquiv hsplit ⟨T₀, hmem⟩`); coefficients `hRT.coef_first/second hη hw (w5t_split' … hsplit) hT hT₁/hT₂ L hL
  (w5t_cutFirst_of/_cutSecond_of … hord hchi … hrot.symm)` with `hrot := w5t_carrierRotation_first/second … hdet ht ht' …` — exactly
  RT's `w5t_spec_factor₁/₂` recipe, split into the two equalities ROW's Prop wants.
* `w5_contactData hloc ht T₀ (hW : s7s_WallTriangleData … (w5s_hx …) (w5s_hy …)) hT : w5r_ContactData hn g h t T₀ hT` —
  `w5s_ContactRowData_e … (w5r_qH …) hW hT hx hy`, then `(s7fc_e …).symm q_H = w5r_qL` by `Equiv.symm_apply_eq` + `w5r_e_qL`
  (rewritten in the hypothesis); `w5s_x` is `w5r_x` by definition.
* `w5_branchData hloc hr hr0 hr1 hη hηr hηr1 ht T₀ hE hT : w5r_BranchData hn g h h₁ h₂ t T₀ hT` — `hRT := w5_returnedData …`;
  `v := w5b_v … hT hRT` with `v.1 = w5r_x hT hx` from `(Equiv.eq_symm_apply _).mpr (Subtype.ext (w5b_v_fst_val …))`; `D_A` and its
  record clause `ι` from the library skein `s7g_cornerHomfly_skein hn hP₂ (lift T₀) (w5r_qH) hT (w5r_x …) v hv`; BR's `q_L`
  (`w5b_qL … hloc ht`) rewritten to `w5r_qL` in BR's data (`unfold w5b_qL; Equiv.symm_apply_eq; w5r_e_qL`); `ε = 1`:
  `w5b_interlacingData … hI hW' DA ι`; `ε = 0`: `w5b_noninterlacingData … hI hW' DA ι` as the FIRST half orientation
  (`Or.inl ⟨v, DA, i, j, hv, Or.inl hb⟩`).  `sorryAx` through BR's three boxes.
* Box bodies (B 24973-25016): `w5r_box_transport` — `s7a2_exists_intervalLocal hn g M a h.1` (`r η hr0 hr1 hr hη hηr hηr1 δ hδ hloc`),
  `s7fb_exists_detRadius hn g h hloc hr hr1 hδ` (`δ' hdet`), `s7f_exists_bigonSplit` (`δ₁ hsplit`), radius `min δ₁ (min δ δ')`;
  `w5r_box_contact` — A2 + `w5s_exists_wall`, radius `min δ₁ δ`; `w5r_box_branch` — A2's radius alone.

### 2.3 The two edits to ROW's block, disclosed (assembler's correction, the analogue of W4 §4's correction to K's recipe)

BR delivers the branch data ONLY under the live selector `wt(q_L) ≠ 0` (`w5b_interlacingData`/`w5b_noninterlacingData` take
`hW : carrierWeight hn hP₀ T₀ (w5b_qL …) ≠ 0`, because the turn fields — U110-C's patterns — are read on a carrier with nonzero
selector, as in the printed argument), while ROW's Prop `w5r_BranchData` was stated unconditionally.  Rather than leave
`w5r_box_branch` sorried and unused, ROW's block was edited in place:
1. **`def w5r_BranchData`** (B 24621) gets one more binder `(_hW : carrierWeight hn (s7f_hP₀ g M a t) T₀ (w5r_qL hn g t T₀) ≠ 0)`
   between `hT₂` and `hx`, and its docstring a sentence on the live selector.  Its two consumers (`w5r_returnedRow_of`, the glue)
   are the only places it is applied.
2. **`w5r_returnedRow_of`** (B 24712): after `rw [hqL, ← mul_sub]` a `by_cases hW : carrierWeight … (w5r_qL …) = 0` is inserted.  In
   the new branch `wt(q_H) = 0` by `w5r_e_qL` + `w5r_carrierWeight_e` (so the left side is `0`), and for `ε = 1` the corner data gives
   `wt(q_H) = −s₀ · wt(L₁) wt(L₂)` (`s7c_carrierWeight_interlacing`), so `wt(L₁) wt(L₂) = 0` (new helper
   **`w5r_prod_eq_zero_of_sgn_mul`**, B 24690, `rcases s₀ <;> simpa`) and the right side is `0` after `w5r_prod_eq_mul_erase` at `L₁`, `L₂`
   (`beta_reduce`, `rcases mul_eq_zero.mp … <;> rw [h0] <;> ring`); for `ε = 0` the right side is `0 · …` (`ite_eq_right`, `ring`).  The
   original proof continues in the `hW ≠ 0` branch with `hBR hT₀ hT₁ hT₂ hW hx hy` (two call sites).  The theorem's statement is
   unchanged; `w4_box_returnedRows`'s body (ROW's) is unchanged.
Everything else in ROW's block is verbatim (14 diff hunks against `W5_ROW.lean`'s block, deleting exactly: the last docstring line of
`w5r_BranchData`, the two `hBR …` call lines, the three closed boxes' docstring lines and `  sorry` bodies, one blank).  The three
closed boxes' docstrings were reworded from "BLACK BOX (unit …)" to "PROVED at assembly (wave 5, from unit …)" with the producer named.
`w5r_box_corners`'s docstring and `w4_box_returnedRows`'s W4 docstring ("BLACK BOX (wave 5 …) … Nothing below depends on the body")
are kept verbatim although the latter now has a body — rewording of closed theorems is a port-time step (task (4) does not apply, §5).

## 3. Task (3): compile, axioms, frozen statements, clash scan

Compile: header (52 s; 0 errors; the 9 `declaration uses sorry` listed there).  `#print axioms` on the scratch copy
`<scratchpad>/w5a/W5A_axioms.lean` (= the file + 33 `#print axioms SM.<name>` lines after `end SM`; 43 s; standard =
`propext, Classical.choice, Quot.sound`; the six registered literature axioms as in `axiom-policy.json`):

| declaration | sorryAx | other axioms | sorryAx source |
|---|---|---|---|
| **`thm_C_S7`** | **YES** | standard + `lit_homfly, lit_homfly_descent, lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact` (the `thm_floor` chain adds the last three) — **exactly the nine registered axioms plus `sorryAx`** | the bigon leaf's `sorry` |
| `thm_C_S7_of_floor`, `thm_C_S7_of` | YES | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` | the bigon leaf |
| `s7_sliding_law_at` | no | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` | — (CLOSED since W4) |
| `s7_bigon_law_at` | YES | standard + `lit_homfly` | its own skeleton `sorry` |
| **`w4_box_returnedRows`** (B2') | YES | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` | `w5r_box_corners`; `w5r_box_branch` → BR's three boxes |
| `w4_s7_bigon_law_at_of`, `w5r_returnedRow_of`, `w5t_returned_terms` | no | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` | — |
| **`w5r_box_transport`**, `w5_transportData` | **no** | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` | — (PROVED) |
| **`w5r_box_contact`**, `w5_contactData`, `w5_returnedData`, `w5s_ContactRowData_e`, `w5s_exists_contactRowData`, `w5t_transport`, `w5r_prod_eq_zero_of_sgn_mul` | **no** | standard only | — (PROVED) |
| `w5_elim_of_symm` | no | `Quot.sound` | — |
| `w5r_box_branch`, `w5_branchData` | YES | standard + `lit_homfly, lp_lm, lp_lm_uniqueness` | BR's `w5b_box_interlacingTurnData`, `w5b_box_noninterlacingTurnData`, `w5b_box_curlData` |
| `w5b_interlacingData` | YES | standard | `w5b_box_interlacingTurnData` |
| `w5b_noninterlacingData` | YES | standard + `lit_homfly, lp_lm` | `w5b_box_noninterlacingTurnData`, `w5b_box_curlData` |
| `w5b_components_of_interlacing`, `w5b_components_of_not_interlacing` | no | standard | — (BR's record fields, PROVED) |
| **`w5r_box_corners`**, **`w5b_box_interlacingTurnData`**, **`w5b_box_noninterlacingTurnData`** | YES (own) | standard | the four OPEN boxes |
| **`w5b_box_curlData`** | YES (own) | standard + `lit_homfly, lp_lm` | |
| `w5b_box_returnedData` | YES (own) | standard | superseded, UNUSED |
| `s7q_box_ret`, `s7z_F_exists`, `s7z_returned_of_FSector` | YES (own) | standard (+ `lit_homfly`) | W3/K superseded, off every proved path |

No unregistered axiom appears anywhere.  Frozen statements: `python3 tools/stmt_check.py W5_Assembled_B.lean --base
W3_Skeleton.lean` → 5/5 byte-identical and unique (PASS); `tail -n 43` = `W3_Skeleton.lean`'s.  Clash scan: `python3
tools/clash_scan.py W5_Assembled_B.lean` → `duplicates_in_assembled: []`, `full_name_clashes: {}` against 702 library files /
23,890 declarations; 1,365 new declarations (W4: 1,028; +146 RT, +20 SITE, +136 BR, +30 ROW incl. the new helper, +5 glue); 45
short-name coincidences, all in different namespaces (the pre-existing `s7r_/s7b_/s7fb_` pairs plus BR's `w5b_GaussSide.*` /
`w5b_GaussSplit.*` members vs library names such as `perm`, `comp`, `nodup`, `sideA`).  The scanner's `prefix_stats` calls `w4_`,
`w5t_`, `w5s_`, `w5b_`, `w5r_`, `w5_` "UNPREFIXED" (its regex knows only `s7[a-z]_`; cosmetic).  Verbatim check (Python, exact line
ranges): W4 lines 7-19853 at B 9-19855; RT/SITE/BR blocks verbatim (§2); ROW block with exactly the §2.3 edits; W4 19854-19857 +
ROW's body + W4 19859-19974 verbatim.  Nothing written under `work/lean`; `lake build` never run; every probe compiled against a
scratch prefix olean (`<scratchpad>/w5a/pfx/W5APrefix.olean` = W4 1-19853 + the four blocks, 46 s).

## 4. Honest state: NOT sorry-free — the exact remaining Props

`thm_C_S7` carries `sorryAx` through `s7_bigon_law_at`'s skeleton `sorry`; wiring the leaf (`w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing
(w4_box_returnedRows hn g h h₁ h₂ hF)`) would move the source to `w4_box_returnedRows`, which carries it through EXACTLY FOUR
declarations (all `∃ δ > 0, ∀ t < δ, ∀ T₀ ∈ w4_EligDec …` resp. per-`t`; vocabulary of W5_ROW_REPORT §3, `q_H = w5r_qH`,
`q_L = w5r_qL`, `L₁ = w5r_L₁`, `L₂ = w5r_L₂`, `T₁ = w5r_T₁`, `T₂ = w5r_T₂`):

1. **`w5r_box_corners`** (ROW, B 24988; `w5r_CornerData hn g h h₁ h₂ t T₀`, B 24571): `∃ (j : ZMod (ccpCornerCount … q_H)) (j₁ : ZMod
   (ccpCornerCount … L₁)) (j₂ : …L₂) (e : {i // i ≠ j₁} ⊕ {i // i ≠ j₂} ≃ {i // i ≠ j}), (∀ x, turn (ccpCornerPolygon … q_H) (e x).1 =
   Sum.elim (turn (ccp L₁) ·.1) (turn (ccp L₂) ·.1) x) ∧ turn (ccp L₁) j₁ = w5r_sgn g M a ∧ turn (ccp L₂) j₂ = w5r_sgn g M a ∧
   turn (ccp q_H) j = (if s7f_Interlacing hn h t then w5r_sgn g M a else -w5r_sgn g M a)` — the contact-corner correspondence
   (sm-4:576-600, eq. s7c:angle-orders).  Geometry: the corner list of `q_H` is, up to a cyclic shift, the images of the corners of
   `L₁` and `L₂` other than their vertices `0`, plus the corner at `μ_M` (RT's `hT.ret` first-return structure and `w5t_ct_*` give the
   corner-list transport for SPECTATORS; the same engine on `q_H` with the glued permutation is what is missing), and the three
   contact turns are the printed signs (W5_ROW_REPORT §3.2's truth check).  Consumed by `w5r_returnedRow_of` (`ε = 1`, C's
   `s7c_carrierWeight_interlacing`) and, in the `wt(q_L) = 0` case, by both `ε`.  Estimate 600-1,000 lines (RT Part D reused).
2. **`w5b_box_interlacingTurnData`** (BR, B 24278; `w5b_InterlacingTurnData hn g h h₁ h₂ t T₀ hloc ht`, B 24248; hypotheses `hT₀ hS₁ hS₂`,
   `hI : s7f_Interlacing`, `hW : wt(w5b_qL) ≠ 0`): `rotation : |carrierRotationInt … (w5b_qL …)| = |carrierRotationInt … L₁| +
   |carrierRotationInt … L₂|`, `pattern₁ : SignedUniformOrOneDissent (ccpCornerPolygon … L₁)`, `pattern₂ : … L₂` (sm-4:655-663; U110-C
   `s7c_uniform_halves_of_interlacing` on the corner correspondence of item 1, U110-I `s7i_interlacing_absolute` on A2's centre polygon
   with `rot L* = rot q_H = rot q_L`).
3. **`w5b_box_noninterlacingTurnData`** (BR, B 24287; `w5b_NoninterlacingTurnData`, B 24259; `hI : ¬ s7f_Interlacing`, `hW`):
   `rotation : |R₁| + |R₂| − |R_L| = −1`, `pattern₁`, `pattern₂` (sm-4:742-757; `s7c_dissent_halves_of_noninterlacing`,
   `s7i_noninterlacing_absolute`).
4. **`w5b_box_curlData`** (BR, B 24304; `w5b_CurlData hn g h h₁ t T₀ hS₁ DA i`, B 24296; hypothesis `hrec : Nonempty (RecordIso
   (DA.knotRestrict i).record (CB.gaussRecord (CB.cg hn hP₂) (insert (s7f_y hn h t) (s7b_img … (carrierCrossings … L₁)))))`):
   `value : SM.P (DA.knotRestrict i) = cornerHomfly … L₁ hS₁`, `writhe : (DA.knotRestrict i).writhe = (carrierCrossingCount … L₁ : ℤ) + 1`
   (sm-4:857-866: the curl `y` is an isolated block of value `1`; cb:products' record-level block product against the blocks of `L₁`;
   the writhe by counting).
Items 2-4 are stated by BR at ITS carriers `w5b_qH`, `w5b_qL … hloc ht`, `w5b_L₁`, `w5b_L₂` (definitionally ROW's; `w5b_qL = w5r_qL` by
`w5r_e_qL`), so their producers need no further glue: `w5_branchData` already consumes `w5b_interlacingData`/`w5b_noninterlacingData`.
Items 1 and 2 share the corner correspondence; one unit should build it for `q_H` from RT's `hT.ret` and both read it.

Sorried but OFF every proved path (draft material, drop at port): `s7q_box_ret` (false as stated, W3), `s7z_F_exists`,
`s7z_returned_of_FSector` (K, superseded by the F-aligned route), `w5b_box_returnedData` (BR; superseded by `w5_returnedData`, §2.1).
Once items 1-4 are proved, `w4_box_returnedRows` is sorry-free and the leaf closes by the one-line body of §0; `thm_C_S7` then rests
on exactly the nine registered axioms.

## 5. Task (4): port — NOT ready

`thm_C_S7` carries `sorryAx` (§3), so `work/drafts/corner/port/CS7/` is not prepared, no superseded declaration is dropped, no
docstring of a still-sorried theorem is reworded beyond §2.3.  For the port once §4 closes: `SM/CS7Units.lean` = B lines 9-25097
minus the row theorems' tail, minus the sorried-and-unused declarations and their shape checks (`s7q_box_ret`, `w3_SlidingRet`,
`w3_SlidingRet_of_box`, `w3_box_rows_of`, `w3_s7_sliding_law_at_of`, `w3_s7_sliding_law_at_of₂`, `s7z_F_exists`,
`s7z_returned_of_FSector`, `s7z_exists_rowSector`, `w3_BigonFSector`, `w3_BigonReturnedRows`, `w3_BigonFSector_of_box`,
`w3_BigonReturnedRows_of_box`, `w3_s7_bigon_law_at_of`, `w5b_box_returnedData`), the "BLACK BOX … NOT proved" docstrings reworded,
the content duplicates of W4 §2 collapsed (`s7u_CarrierData'` ≡ `s7g_CarrierData'`; B3's `s7o_side_of_r`/`s7o_sideData`/
`s7o_persistent_of_ne` ≡ FB1's; K's `s7z_side/x/y/dirSign` ≡ F's; wave 5 adds `w5t_qH ≡ w5r_qH ≡ w5b_qH`, `w5t_L₁/L₂ ≡ w5r_L₁/L₂ ≡
w5b_L₁/L₂`, `w5t_T₁/T₂ ≡ w5r_T₁/T₂`, `w5t_hcx/hcy ≡ w5b_hcx/hcy`, `w5s_hx ≡ w5b_hx`, `w5s_x ≡ w5r_x`, `w5b_qL ≡ w5s_qL`); split into two
modules if one exceeds ~90 s (the whole file compiles in 52 s at load ≈ 4, so likely one); `SM/CS7.lean` = the two leaves,
`thm_C_S7_of`, `thm_C_S7_of_floor`, `theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor`; `SM/ComparisonRows.lean` (rows
127/128) = `theorem thm_comparison (hR : hyp_R) : … := thm_comparison_of hR thm_C_S7 thm_C_soft` and `theorem cor_C_inherits (hR : hyp_R)
: CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft` with the FIXED statements of `work/drafts/comparison/Comparison_Assembled.lean`
1009-1020 (`thm_comparison_of` = `work/lean/SM/Comparison.lean:233`, `cor_C_inherits_of` = `work/lean/SM/CInherits.lean:135`).

## 6. The parallel assembly `W5_Assembled.lean` (canonical name; second assembler, scratch `w5asm/`) — independently verified here

* Its file (sha256 `69b01559…`, 25,237 lines, unchanged between 11:11:56Z and 11:25Z) compiled here: **0 errors, 53 s, exactly 10
  `declaration uses sorry`** (4439, 18055, 18496, 23881, 24278, 24287, 24304, 25071 `w5r_box_corners`, 25090 `w5r_box_branch`, 25185
  the leaf); `stmt_check --base W3_Skeleton.lean` 5/5 PASS; `clash_scan` clean (1,366 new declarations, no duplicates, no full-name
  clashes).  Its own `axioms.log` (scratch `w5asm/`) shows `thm_C_S7` on the same list as §3 and `sorryAx` entering
  `w4_box_returnedRows` through the same four open boxes.
* Design difference, the only one: it keeps ROW's block VERBATIM (so ROW's unconditional `w5r_box_branch` stays sorried and UNUSED — its
  tenth sorry) and adds to the glue `w5_returnedRow_of` (ROW's row with the `wt(q_L) = 0` case handled, delegating otherwise to
  `w5r_returnedRow_of`), `w5_box_branch` (the live-selector restatement of `w5r_box_branch`) and `w5_signType_cast_ne_zero`, and gives
  `w4_box_returnedRows` its own composition; here ROW's Prop and row carry the live selector themselves (§2.3), `w5r_box_branch` is
  proved in place and no glue duplicates ROW's row (9 sorried bodies, 5 glue declarations vs 10 and 7).  Same units, same theorems
  proved, same four open Props, same closure line; both leave `w5b_box_returnedData` superseded.  Wave 6 can start from either; if
  B is adopted, rename `W5_Assembled_B.lean` → `W5_Assembled.lean` and this report accordingly (line numbers in §2-§4 are B's).

## 7. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W5_BR.lean            # 0 errors, 37 s, 9 sorry notes (unit BR had no report)
cd work/lean && lake env lean ../drafts/corner/W5_Assembled_B.lean   # 0 errors, 52 s, 9 sorry notes: 4439 18055 18496 23881 24278 24287 24304 24988 25107
cd work/lean && lake env lean <scratchpad>/w5a/W5A_axioms.lean       # 43 s; the table of §3 (thm_C_S7: nine registered axioms + sorryAx)
python3 tools/stmt_check.py W5_Assembled_B.lean --base W3_Skeleton.lean   # 5/5 PASS
python3 tools/clash_scan.py W5_Assembled_B.lean                           # duplicates [] / full_name_clashes {}
diff W4_Assembled.lean W5_Assembled_B.lean | grep '^[0-9]'                # 1,6c1,8  19853a19856,25018  19858c25023,25043
tail -n 43 W5_Assembled_B.lean | cmp - <(tail -n 43 W3_Skeleton.lean)     # identical
grep -c sorry W5_Assembled_B.lean                                          # 21 (9 bodies + 12 prose)
```
Scratch (`<scratchpad>/w5a/`): `row_block.lean` (ROW's block with §2.3), `glue.lean`, `box_bodies.lean`, `pfx/W5APrefix.{lean,olean}`,
`lean.sh` (the pinned `lean` binary with the project `LEAN_PATH` + `pfx/`; `lean -o` must run from the scratch dir), `Probe1.lean`
(the glue against the prefix, 3 `rw` failures on mixed spellings → `w5_elim_of_symm` and term-mode `Iff.mpr`, then clean),
`W5A_Assembled.lean` (= B before the header), `W5A_axioms.lean`, `compile_*.log`, `axioms_W5A.log`, `clash_*.json`,
`Other_W5_Assembled.lean` (the canonical file as copied at 11:14Z).  Timeline (UTC): 10:44 start (reports, unit diffs, interfaces);
10:47 BR compile; 10:59 ROW edits; 11:05 prefix olean; 11:09 probe 1 (3 errors); 11:12 probe 2 clean; 11:14 canonical file found;
11:16-11:22 assembly B, compile, axioms, checks of both files; 11:25 report.
